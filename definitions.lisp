(in-package "MAT")

(include-book "centaur/fty/top" :dir :system)

(fty::defprod melem
              ((r natp :default '0)
               (c natp :default '0)
               (val rationalp :default '0)))
(fty::deflist melems
              :elt-type melem
              :true-listp t)

(defthmd melems-p-of-append
  (implies (true-listp a)
           (equal (melems-p (append a b))
                  (and (melems-p a)
                       (melems-p b)))))

(fty::defprod matrix
              ((rows natp :default '0)
               (cols  natp :default '0)
               (elems  melems-p)))

;; Using (matrix->fix nil), i.e., (matrix 0 0 nil), instead of nil.
(fty::defoption maybe-melem melem)

(define m-get ((m matrix-p)
               (r natp)
               (c natp))
  :returns (elem rationalp :rule-classes :type-prescription)
  :prepwork
  ((define m-get-aux ((elems melems-p)
                      (r natp)
                      (c natp))
     :returns (elem maybe-melem-p)
     (b* (((when (or (atom elems) (zp r) (zp c)))
           nil)
          ((melem x) (melem-fix (car elems)))
          ((when (and (equal r x.r) (equal c x.c)))
           x))
       (m-get-aux (cdr elems) r c))
     ///
     (defthm m-get-aux-special-cases
       (and (implies (and (case-split (not (equal r 0))) (case-split (zp r)))
                     (equal (m-get-aux m r c)
                            (m-get-aux m 0 c)))
            (implies (and (case-split (not (equal c 0))) (case-split (zp c)))
                     (equal (m-get-aux m r c)
                            (m-get-aux m r 0))))
       :hints (("Goal" :in-theory (e/d (m-get-aux) ()))))
     (defthm m-get-aux-append
       (equal (m-get-aux (append ls1 ls2) r c)
              (or (m-get-aux ls1 r c)
                  (m-get-aux ls2 r c))))))
  (b* (((matrix m))
       (r (lnfix r))
       (c (lnfix c))
       ((unless (and (<= r m.rows) (<= c m.cols) (< 0 r) (< 0 c)))
        0)
       (x (m-get-aux m.elems r c))
       ((unless x)
        0)
       ((melem x) x))
    x.val)

  ///
  (defthm m-get-special-cases
    (implies (case-split (or (zp r) (zp c)
                             (< (matrix->rows m1) r)
                             (< (matrix->cols m1) c)))
             (equal (m-get m1 r c)
                    0))))

;; Matrix Equality
(define m-=--cols ((m1 matrix-p)
                   (m2 matrix-p)
                   (r natp)
                   (c natp))
  :returns (eqp booleanp :rule-classes :type-prescription)
  (if (or (zp c) (zp r))
      t
    (and (equal (m-get m1 r c) (m-get m2 r c))
         (m-=--cols m1 m2 r (1- c)))))


(define m-=--rows ((m1 matrix-p)
                   (m2 matrix-p)
                   (r natp))
  :returns (eqp booleanp :rule-classes :type-prescription)
  (b* (((matrix m1))
       ((matrix m2)))
    (if (zp r)
        (equal m1.cols m2.cols)
      (and (equal m1.cols m2.cols)
           (m-=--cols m1 m2 r m1.cols)
           (m-=--rows m1 m2 (1- r))))))

(define m-= ((m1 matrix-p)
             (m2 matrix-p))
  :returns (eqp booleanp :rule-classes :type-prescription)
  (b* (((matrix m1))
       ((matrix m2)))
    (and (equal m1.rows m2.rows)
         (m-=--rows m1 m2 m1.rows))))


;; Matrix Sum

(define summable-p ((m1 matrix-p)
                    (m2 matrix-p))
  :returns (b booleanp :rule-classes :type-prescription)
  (and (equal (matrix->rows m1) (matrix->rows m2))
       (equal (matrix->cols m1) (matrix->cols m2))))

(define m-+--cols ((m1 matrix-p)
                   (m2 matrix-p)
                   (row natp)
                   (cols natp))
  :returns (val melems-p)
  :short "Elements (m1 + m2)[row, :cols]"
  (if (and (summable-p m1 m2) (not (zp row)) (not (zp cols)))
    (cons (make-melem :r row :c cols
                      :val (+ (m-get m1 row cols) (m-get m2 row cols)))
          (m-+--cols m1 m2 row (1- cols)))
    nil))

(define m-+--rows ((m1 matrix-p)
                   (m2 matrix-p)
                   (rows natp))
  :returns (val melems-p
                :hints (("Goal" :in-theory (e/d (melems-p-of-append) ()))))
  :short "Elements (m1 + m2)[:row, :]"
  (if (and (summable-p m1 m2) (not (zp rows)))
      (append (m-+--cols m1 m2 rows (matrix->cols m1))
              (m-+--rows m1 m2 (1- rows)))
    nil))

(define m-+ ((m1 matrix-p)
             (m2 matrix-p))
  :returns (p matrix-p)
  :short "Matrix Sum"
  (b* (((matrix m1))
       ((matrix m2))
       ((unless (summable-p m1 m2))
        (make-matrix :rows 0 :cols 0 :elems nil)))
    (make-matrix :rows m1.rows :cols m2.cols
                 :elems (m-+--rows m1 m2 m1.rows)))
  ///
  (defthm m-+-rows-cols
    (implies (summable-p m1 m2)
             (and (equal (matrix->rows (m-+ m1 m2)) (matrix->rows (double-rewrite m1)))
                  (equal (matrix->cols (m-+ m1 m2)) (matrix->cols (double-rewrite m1)))))
  :hints (("Goal" :in-theory (e/d (summable-p) ())))))

(define zeros-r-c ((r natp)
                   (c natp))
  :returns (zeros-m matrix-p)
  (make-matrix :rows (lnfix r) :cols (lnfix c) :elems nil)

  ///
  (defthm zeros-rows-cols
    (and (equal (matrix->rows (zeros-r-c r c)) (nfix (double-rewrite r)))
         (equal (matrix->cols (zeros-r-c r c)) (nfix (double-rewrite c))))
    :hints (("Goal" :in-theory (e/d (m-+) ()))))

  (defthm zeros-r-c-get
    (equal (m-get (zeros-r-c rows cols) r c)
           0)
    :hints (("Goal" :in-theory (e/d (m-get m-get-aux) ())))))

(define zeros ((n natp))
  :returns (zeros-m matrix-p)
  (zeros-r-c n n))


;; Matrix Product
(define dot-prod ((m1 matrix-p)
                  (m2 matrix-p)
                  (row natp)
                  (col natp)
                  (n natp))
  :returns (val rationalp)
  :short "Dot-product of m1[row, :n] and m2 [:n, col]"
  (b* ((row (lnfix row))
       (col (lnfix col)))
    (if (zp n)
        0
      (+ (* (m-get m1 row n) (m-get m2 n col))
         (dot-prod m1 m2 row col (1- n)))))

  ///
  (defthm dot-prod-zp-r-or-c
    (implies (or (zp r) (zp c) (< (matrix->rows m1) r) (< (matrix->cols m2) c))
             (equal (dot-prod m1 m2 r c size)
                    0))))

(define mult-p ((m1 matrix-p)
                (m2 matrix-p))
  :returns (b booleanp :rule-classes :type-prescription)
  (b* (((matrix m1))
       ((matrix m2)))
    (equal m1.cols m2.rows)))

(define m-*--cols ((m1 matrix-p)
                      (m2 matrix-p)
                      (row natp)
                      (cols natp))
     :returns (val melems-p)
     :short "Elements (m1 * m2)[row, :cols]"
     (b* (((unless (and (mult-p m1 m2) (not (zp row)) (not (zp cols))))
           nil)
          ((matrix m1)))
       (cons (make-melem :r row :c cols :val (dot-prod m1 m2 row cols m1.cols))
             (m-*--cols m1 m2 row (1- cols)))))

(define m-*--rows ((m1 matrix-p)
                   (m2 matrix-p)
                   (rows natp))
  :returns (val melems-p
                :hints (("Goal" :in-theory (e/d (melems-p-of-append) ()))))
  :short "Elements (m1 * m2)[:rows, :]"
  (b* (((unless (and (mult-p m1 m2) (not (zp rows))))
        nil)
       ((matrix m2)))
    (append (m-*--cols m1 m2 rows m2.cols)
            (m-*--rows m1 m2 (1- rows)))))

(define m-* ((m1 matrix-p)
             (m2 matrix-p))
  :returns (p matrix-p)
  :short "Matrix Product"
  :prepwork
  ()

  (b* (((unless (mult-p m1 m2))
        (make-matrix :rows 0 :cols 0 :elems nil))
       ((matrix m1))
       ((matrix m2)))
    (make-matrix :rows m1.rows :cols m2.cols
                 :elems (m-*--rows m1 m2 m1.rows)))

  ///
  (defthm m-*-rows-cols
    (implies (mult-p m1 m2)
             (and (equal (matrix->rows (m-* m1 m2)) (matrix->rows (double-rewrite m1)))
                  (equal (matrix->cols (m-* m1 m2)) (matrix->cols
                                                     (double-rewrite m2)))))
    :hints (("Goal" :in-theory (e/d (mult-p) ()))))
  (defthm m-*-zp-rows
    (implies (zp (matrix->rows (double-rewrite m1)))
             (equal (matrix->rows (m-* m1 m2)) 0)))
  (defthm m-*-zp-cols
    (implies (zp (matrix->cols (double-rewrite m2)))
             (equal (matrix->cols (m-* m1 m2)) 0)))
  (defthm m-*-matrix-fix
  (implies (equal (matrix->cols (double-rewrite m1)) (matrix->rows (double-rewrite m2)))
           (equal (matrix-fix (m-* m1 m2)) (m-* m1 m2)))))

(define iden-aux ((n natp))
  :returns (melems melems-p)
  (if (zp n)
      nil
    (cons (make-melem :r n :c n :val 1) (iden-aux (1- n)))))

(define iden ((n natp))
  :returns (id-n matrix-p)
  :short "The identity matrix"
  (make-matrix :rows n :cols n :elems (iden-aux n))

  ///
  (defthm iden-rows-cols
    (and (equal (matrix->rows (iden n)) (nfix (double-rewrite n)))
         (equal (matrix->cols (iden n)) (nfix (double-rewrite n))))))


;; Auxilliary functions
(define is_square ((m matrix-p))
  :returns (b booleanp)
  (equal (matrix->rows m) (matrix->cols m)))

(define transpose-aux ((elems melems-p))
  :returns (elems melems-p)
  (b* (((unless (consp elems))
         nil)
       ((melem elem) (melem-fix (car elems))))
    (cons (make-melem :r elem.c :c elem.r :val elem.val)
          (transpose-aux (cdr elems))))

  ///
  (defthm transpose-involutive-aux
    (equal (transpose-aux (transpose-aux m)) (melems-fix m)))

  (defthm transpose-m-get-aux
    (equal (melem->val (m-get-aux (transpose-aux m1) c r))
           (melem->val (m-get-aux (melems-fix m1) r c)))
    :hints (("Goal" :in-theory (e/d (m-get-aux) ())
                    :expand ((m-get-aux (melems-fix m1) r c))
                    ;;          (m-get-aux (melems-fix (cdr m1)) c r))
                    ))))

(define transpose ((m matrix-p))
  :returns (m matrix-p)
  (b* (((matrix m)))
    (make-matrix :rows m.cols :cols m.rows :elems (transpose-aux m.elems)))

  ///
  (defthm transpose-involutive
    (equal (transpose (transpose m)) (matrix-fix m)))

  (defthm transpose-m-get
    (equal (m-get (transpose m1) c r)
           (m-get (matrix-fix m1) r c))
    :hints (("Goal" :in-theory (e/d (m-get) (transpose-m-get-aux))
                    :use ((:instance transpose-m-get-aux
                           (m1 (matrix->elems m1)))))))

  (defthm transpose-rows-cols
    (and (equal (matrix->rows (transpose m)) (matrix->cols (matrix-fix m)))
         (equal (matrix->cols (transpose m)) (matrix->rows (matrix-fix m))))))

;; (define pivot ((m matrix-p)
;;                (row natp)
;;                (col natp)
;;                (arg-max natp))
;;   :returns (mv (a-max natp) (max-val rationalp))
;;   :measure (let ((row (nfix row))
;;                  (rows (matrix->rows m)))
;;              (if (< rows row) 0 (+ 1 rows (- row))))
;;   (if (or (zp row) (zp col) (< (matrix->rows m) row) (< (matrix->cols m) col))
;;       (mv (lnfix arg-max) (m-get m arg-max col))
;;     (if (< (abs (m-get m arg-max col)) (abs (m-get m row col)))
;;         (pivot m (1+ row) col row)
;;       (pivot m (1+ row) col arg-max))))

(define row-perm ((m matrix-p)
                  (r1 natp)
                  (r2 natp))
  :returns (mat matrix-p)
  :prepwork
  ((define row-perm-aux ((m melems-p)
                         (r1 natp)
                         (r2 natp))
     :returns (m-elems melems-p)
     (if (consp m)
         (b* (((melem e) (melem-fix (car m)))
              (r1 (lnfix r1))
              (r2 (lnfix r2))
              (rest (cdr m))
              (rest (row-perm-aux rest r1 r2))
              (target (cond ((equal e.r r1) r2)
                            ((equal e.r r2) r1)
                            (t e.r))))
           (if (or (equal target 0) (equal e.r 0))
               rest
             (cons (make-melem :r target :c e.c :val e.val) rest)))
       nil)))

  (b* ((r1 (cond ((zp r1) 0)
                 ((< (matrix->rows m) r1) 0)
                 (t r1)))
       (r2 (cond ((zp r2) 0)
                 ((< (matrix->rows m) r2) 0)
                 (t r2))))
    (make-matrix :rows (matrix->rows m) :cols (matrix->cols m)
                 :elems (row-perm-aux (matrix->elems m) r1 r2)))

  ///
  (defthm row-perm-row-col
    (and (equal (matrix->rows (row-perm m r1 r2)) (matrix->rows m))
         (equal (matrix->cols (row-perm m r2 r2)) (matrix->cols m))))
  (defthm row-perm-aux-special-cases-1
    (implies (and (zp r1) (case-split (not (equal r1 0))))
                  (equal (row-perm-aux m r1 r2)
                         (row-perm-aux m 0 r2)))
    :hints (("Goal" :in-theory (e/d (row-perm-aux) ()))))
  (defthm row-perm-aux-special-cases-2
    (implies (and (zp r2) (case-split (not (equal r2 0))))
                  (equal (row-perm-aux m r1 r2)
                         (row-perm-aux m r1 0)))
    :hints (("Goal" :in-theory (e/d (row-perm-aux) ())))))

(define col-perm ((m matrix-p)
                  (r1 natp)
                  (r2 natp))
  :returns (mat matrix-p)
  :prepwork
  ((define col-perm-aux ((m melems-p)
                         (r1 natp)
                         (r2 natp))
     :returns (m-elems melems-p)
     (if (consp m)
         (b* (((melem e) (melem-fix (car m)))
              (r1 (lnfix r1))
              (r2 (lnfix r2))
              (rest (cdr m))
              (rest (col-perm-aux rest r1 r2))
              (target (cond ((equal e.r r1) r2)
                            ((equal e.r r2) r1)
                            (t e.r))))
           (if (or (equal target 0) (equal e.r 0))
               rest
             (cons (make-melem :r target :c e.c :val e.val) rest)))
       nil)))

  (b* ((r1 (cond ((zp r1) 0)
                 ((< (matrix->cols m) r1) 0)
                 (t r1)))
       (r2 (cond ((zp r2) 0)
                 ((< (matrix->cols m) r2) 0)
                 (t r2))))
    (make-matrix :rows (matrix->rows m) :cols (matrix->cols m)
                 :elems (col-perm-aux (matrix->elems m) r1 r2)))

  ///
  (defthm col-perm-row-col
    (and (equal (matrix->rows (col-perm m r1 r2)) (matrix->rows m))
         (equal (matrix->cols (col-perm m r2 r2)) (matrix->cols m)))))
