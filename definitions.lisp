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
;; (fty::defoption maybe-matrix matrix)

(define m-get-aux ((elems melems-p)
                      (r natp)
                      (c natp))
  :returns (elem rationalp
                 :rule-classes :type-prescription)
  (b* (((when (or (atom elems) (zp r) (zp c)))
        0)
       ((melem x) (car elems))
       ((when (and (equal r x.r) (equal c x.c)))
        x.val))
    (m-get-aux (cdr elems) r c)))

(define m-get ((m matrix-p)
                  (r natp)
                  (c natp))
  :returns (elem rationalp :rule-classes :type-prescription)
  (b* (((matrix m))
       (r (lnfix r))
       (c (lnfix c))
       ((unless (and (<= r m.rows) (<= c m.cols) (< 0 r) (< 0 c)))
        0))
    (m-get-aux m.elems r c))

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
  (if (zp c)
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

;; Matrix Product
(define dot-prod ((m1 matrix-p)
                  (m2 matrix-p)
                  (row natp)
                  (col natp)
                  (n natp))
  :returns (val rationalp)
  :short "Dot-product of m1[row, :n] and m2 [:n, col]"
  (if (zp n)
      0
    (+ (* (m-get m1 row n) (m-get m2 n col))
       (dot-prod m1 m2 row col (1- n))))

  ///
  (defthm dot-prod-zp-r-or-c
    (implies (or (zp r) (zp c) (< (matrix->rows m1) r) (< (matrix->cols m2) c))
             (equal (dot-prod m1 m2 r c size)
                    0))))

(define m-*--cols ((m1 matrix-p)
                   (m2 matrix-p)
                   (row natp)
                   (cols natp))
  :returns (val melems-p)
  :short "Elements (m1 * m2)[row, :cols]"
  (b* (((matrix m1)))
    (if (zp cols)
        nil
      (cons (make-melem :r row :c cols :val (dot-prod m1 m2 row cols m1.cols))
            (m-*--cols m1 m2 row (1- cols))))))

(define m-*--rows ((m1 matrix-p)
                   (m2 matrix-p)
                   (rows natp))
  :returns (val melems-p
                :hints (("Goal" :in-theory (e/d (melems-p-of-append) ()))))
  :short "Elements (m1 * m2)[:rows, :]"
  (b* (((matrix m2)))
    (if (zp rows)
        nil
      (append (m-*--cols m1 m2 rows m2.cols)
              (m-*--rows m1 m2 (1- rows))))))

(define m-* ((m1 matrix-p)
             (m2 matrix-p))
  :returns (p matrix-p)
  :short "Matrix Product"
  (b* (((matrix m1))
       ((matrix m2))
       ((unless (equal m1.cols m2.rows))
        (make-matrix :rows 0 :cols 0 :elems nil)))
    (make-matrix :rows m1.rows :cols m2.cols
                 :elems (m-*--rows m1 m2 m1.rows)))

  ///
  (defthm m-*-rows-cols
    (implies (equal (matrix->cols m1) (matrix->rows m2))
             (and (equal (matrix->rows (m-* m1 m2)) (matrix->rows m1))
                  (equal (matrix->cols (m-* m1 m2)) (matrix->cols m2)))))
  (defthm m-*-zp-rows
    (implies (zp (matrix->rows m1))
             (equal (matrix->rows (m-* m1 m2)) 0)))
  (defthm m-*-zp-cols
    (implies (zp (matrix->cols m2))
             (equal (matrix->cols (m-* m1 m2)) 0)))
  (defthm m-*-matrix-fix
  (implies (equal (matrix->cols m1) (matrix->rows m2))
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
    (and (equal (matrix->rows (iden n)) (nfix n))
         (equal (matrix->cols (iden n)) (nfix n)))))

;; Matrix Sum
(define m-+--cols ((m1 matrix-p)
                   (m2 matrix-p)
                   (row natp)
                   (cols natp))
  :returns (val melems-p)
  :short "Elements (m1 + m2)[row, :cols]"
  (if (zp cols)
      nil
    (cons (make-melem :r row :c cols
                      :val (+ (m-get m1 row cols) (m-get m2 row cols)))
          (m-+--cols m1 m2 row (1- cols)))))

(define m-+--rows ((m1 matrix-p)
                   (m2 matrix-p)
                   (rows natp))
  :returns (val melems-p
                :hints (("Goal" :in-theory (e/d (melems-p-of-append) ()))))
  :short "Elements (m1 + m2)[:row, :]"
  (if (or (zp rows) (not (equal (matrix->cols m1) (matrix->cols m2))))
      nil
    (append (m-+--cols m1 m2 rows (matrix->cols m1))
            (m-+--rows m1 m2 (1- rows)))))

(define m-+ ((m1 matrix-p)
             (m2 matrix-p))
  :returns (p matrix-p)
  :short "Matrix Sum"
  (b* (((matrix m1))
       ((matrix m2))
       ((unless (and (equal m1.rows m2.rows) (equal m1.cols m2.cols)))
        (make-matrix :rows 0 :cols 0 :elems nil)))
    (make-matrix :rows m1.rows :cols m2.cols
                 :elems (m-+--rows m1 m2 m1.rows)))
  ///
  (defthm m-+-rows-cols
  (implies (and (equal (matrix->rows m1) (matrix->rows m2))
                (equal (matrix->cols m1) (matrix->cols m2)))
           (and (equal (matrix->rows (m-+ m1 m2)) (matrix->rows m1))
                (equal (matrix->cols (m-+ m1 m2)) (matrix->cols m1))))
  :hints (("Goal" :in-theory (e/d () ())))))

(define zeros-r-c ((r natp)
                   (c natp))
  :returns (zeros-m matrix-p)
  (make-matrix :rows (lnfix r) :cols (lnfix c) :elems nil)

  ///
  (defthm zeros-rows-cols
    (and (equal (matrix->rows (zeros-r-c r c)) (nfix r))
         (equal (matrix->cols (zeros-r-c r c)) (nfix c)))
    :hints (("Goal" :in-theory (e/d (m-+) ()))))

  (defthm zeros-r-c-get
    (equal (m-get (zeros-r-c rows cols) r c)
           0)
    :hints (("Goal" :in-theory (e/d (m-get m-get-aux) ())))))

(define zeros ((n natp))
  :returns (zeros-m matrix-p)
  (zeros-r-c n n))

;; Auxilliary functions
(define is_square ((m matrix-p))
  :returns (b booleanp)
  (equal (matrix->rows m) (matrix->cols m)))

(define transpose-aux ((elems melems-p))
  :returns (elems melems-p)
  (b* (((unless (consp elems))
         nil)
       ((melem elem) (car elems)))
    (cons (make-melem :r elem.c :c elem.r :val elem.val)
          (transpose-aux (cdr elems))))

  ///
  (defthm transpose-involutive-aux
    (equal (transpose-aux (transpose-aux m)) (melems-fix m)))

  (defthm transpose-m-get-aux
    (equal (m-get-aux (transpose-aux m1) r c)
           (m-get-aux (melems-fix m1) c r))
    :hints (("Goal" :in-theory (e/d (m-get-aux) ())))))

(define transpose ((m matrix-p))
  :returns (m matrix-p)
  (b* (((matrix m)))
    (make-matrix :rows m.cols :cols m.rows :elems (transpose-aux m.elems)))

  ///
  (defthm transpose-involutive
    (equal (transpose (transpose m)) (matrix-fix m)))

  (defthm transpose-m-get
    (equal (m-get (transpose m1) r c)
           (m-get (matrix-fix m1) c r))
    :hints (("Goal" :in-theory (e/d (m-get) ()))))

  (defthm transpose-rows-cols
    (and (equal (matrix->rows (transpose m)) (matrix->cols (matrix-fix m)))
         (equal (matrix->cols (transpose m)) (matrix->rows (matrix-fix m))))))
