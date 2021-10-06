;; Matrix product theorems

(in-package "MAT")

(include-book "definitions")
(include-book "equality")

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (e/d (m-=--rows m-=--cols) ())))

(defcong m-= equal (dot-prod m1 m2 row col size) 1
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))
          ("Subgoal *1/2.1.2" :in-theory (e/d (m-get) ()))
          ("Subgoal *1/2.1.1" :in-theory (e/d (m-get) ()))))

(defcong m-= equal (m-*--cols m1 m2 row col) 1
  :hints (("Goal" :in-theory (e/d (m-*--cols) ()))))

(defcong m-= equal (m-*--rows m1 m2 row) 1
  :hints (("Goal" :in-theory (e/d (m-*--rows) ()))))

(defcong m-= equal (m-* m1 m2) 1
  :hints (("Goal" :in-theory (e/d (m-*) ()))))

(defcong m-= equal (dot-prod m1 m2 row col size) 2
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))
          ("Subgoal *1/2.1.2" :in-theory (e/d (m-get) ()))
          ("Subgoal *1/2.1.1" :in-theory (e/d (m-get) ()))))

(defcong m-= equal (m-*--cols m1 m2 row col) 2
  :hints (("Goal" :in-theory (e/d (m-*--cols) ()))))

(defcong m-= equal (m-*--rows m1 m2 row) 2
  :hints (("Goal" :in-theory (e/d (m-*--rows) ()))))

(defcong m-= equal (m-* m1 m2) 2
  :hints (("Goal" :in-theory (e/d (m-*) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Multiplicative identity
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm m-get-iden-aux
  (equal (m-get-aux (iden-aux n) r c)
         (if (or (zp r) (zp c) (zp n) (< n r) (< n c))
             0
           (if (equal r c)
               1 0)))
  :hints (("Goal" :in-theory (e/d (m-get-aux iden-aux) ()))))

(defthm m-get-iden
  (equal (m-get (iden n) r c)
         (if (or (zp r) (zp c) (zp n) (< n r) (< n c))
             0
           (if (equal r c)
               1 0)))
  :hints (("Goal" :in-theory (e/d (m-get iden) ()))))

(defthmd dot-prod-iden-right
  (equal (dot-prod m1 (iden n) r c size)
         (if (or (zp size) (zp c) (zp n) (< size c) (< n c))
             0
           (m-get m1 r c)))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthmd dot-prod-iden-left
  (equal (dot-prod (iden n) m1 r c size)
         (if (or (zp size) (zp r) (zp n) (< size r) (< n r))
             0
           (m-get m1 r c)))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthm m-*-get-dot-prod-cols
  (implies (and (natp cols) (<= c cols))
           (equal (m-get-aux (m-*--cols m1 m2 r cols) r c)
                  (dot-prod m1 m2 r c (matrix->cols m1))))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-*--cols) ()))))

(defthm m-*-row-append-get-aux-1
  (implies (and (natp col) (<= c col))
           (equal (m-get-aux (append (m-*--cols m1 m2 row col) ls) row c)
                  (m-get-aux (m-*--cols m1 m2 row c) row c)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-*--cols) ()))))

(defthm m-*-row-append-get-aux-2
  (implies (or (not (equal row r)) (< col c))
           (equal (m-get-aux (append (m-*--cols m1 m2 row col) ls) r c)
                  (m-get-aux ls r c)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-*--cols) ()))))

(defthm m-*-get-cols-out-of-bounds
  (implies (< (matrix->cols m2) c)
           (equal (m-get-aux (m-*--rows m1 m2 rows) r c)
                  0))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-*--rows) ()))))

(defthm m-*-get-dot-prod-rows
  (implies (and (natp r) (natp rows) (<= r rows) (natp c))
           (equal (m-get-aux (m-*--rows m1 m2 rows) r c)
                  (dot-prod m1 m2 r c (matrix->cols m1))))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-*--rows) ()))
          ("Subgoal *1/5" :cases ((equal r rows)))
          ("Subgoal *1/5.1'" :cases ((<= c (matrix->cols m2))))
          ("Subgoal *1/4''" :cases ((<= c (matrix->cols m2))))))

(defthm m-*-get-dot-prod
  (implies (equal (matrix->cols m1) (matrix->rows m2))
           (equal (m-get (m-* m1 m2) r c)
                  (dot-prod m1 m2 r c (matrix->cols m1))))
  :hints (("Goal" :in-theory (e/d (m-get m-*) ()))))

(defthm m-*-iden-right-cols
  (m-=--cols (m-* m1 (iden (matrix->cols m1))) m1 r c)
  :hints (("Subgoal *1/3" :cases ((zp (matrix->cols m1))))
          ("Subgoal *1/3.2" :in-theory (e/d (dot-prod-iden-right) ()))
          ("Subgoal *1/3.1" :in-theory (e/d (m-get m-*) ()))))

(defthm m-*-iden-right-rows
  (m-=--rows (m-* m1 (iden (matrix->cols m1))) m1 r))

(defthm m-*-iden-right
  (m-= (m-* m1 (iden (matrix->cols m1))) m1)
  :hints (("Goal" :in-theory (e/d (m-=) ()))))

(defthm m-*-iden-left-cols
  (m-=--cols (m-* (iden (matrix->rows m1)) m1) m1 r c)
  :hints (("Goal" :in-theory (e/d (dot-prod-iden-left) ()))))

(defthm m-*-iden-left-rows
  (m-=--rows (m-* (iden (matrix->rows m1)) m1) m1 r))

(defthm m-*-iden-left
  (m-= (m-* (iden (matrix->rows m1)) m1) m1)
  :hints (("Goal" :in-theory (e/d (m-=) ()))))


;;;; Transpose of products

(defthm trans-prod-dot-prod-trans
  (implies (equal (matrix->cols m1) (matrix->rows m2))
           (equal (dot-prod (transpose m2) (transpose m1) r c size)
                  (dot-prod (matrix-fix m1) (matrix-fix m2) c r size)))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthm trans-prod-prod-trans-cols
  (implies (and (equal (matrix->cols m1) (matrix->rows m2)) (matrix-p m1) (matrix-p m2))
           (m-=--cols (transpose (m-* m1 m2))
                      (m-* (transpose m2) (transpose m1)) r c)))

(defthm trans-prod-prod-trans-rows
  (implies (and (equal (matrix->cols m1) (matrix->rows m2)) (matrix-p m1) (matrix-p m2))
           (m-=--rows (transpose (m-* m1 m2))
                      (m-* (transpose m2) (transpose m1)) r))
  :hints (("Goal" :in-theory (e/d () ()))))


(defthm trans-m-*-m-*-trans
  (implies (and (equal (matrix->cols m1) (matrix->rows m2)) (matrix-p m1) (matrix-p m2))
           (m-= (transpose (m-* m1 m2))
                (m-* (transpose m2) (transpose m1))))
  :hints (("Goal" :in-theory (e/d (m-=) ()))))


;; Product distributes over sum
(local (include-book "sum"))

(defthm m-*-dist-m-+-dot-prod
  (implies (and (equal (matrix->cols m1)
                     (matrix->rows m2))
              (equal (matrix->cols m1)
                     (matrix->rows m3))
              (equal (matrix->cols m2)
                     (matrix->cols m3)))
         (equal (dot-prod m1 (m-+ m2 m3)
                          r c s)
                (+ (dot-prod m1 m2 r c s)
                   (dot-prod m1 m3 r c s))))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthm m-*-dist-m-+-get
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m1) (matrix->rows m3))
                (equal (matrix->cols m2) (matrix->cols m3)))
           (equal (m-get (m-* m1 (m-+ m2 m3)) r c)
                  (+ (m-get (m-* m1 m2) r c)
                     (m-get (m-* m1 m3) r c))))
  :hints (("Goal" :use ((:instance m-+-rows-cols
                         (m1 m2)
                         (m2 m3))))))

(defthm m-*-dist-m-+-cols
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m1) (matrix->rows m3))
                (equal (matrix->cols m2) (matrix->cols m3)))
           (equal (m-*--cols m1 (m-+ m2 m3) r c)
                  (m-+--cols (m-* m1 m2) (m-* m1 m3) r c)))
  :hints (("Goal" :in-theory (e/d (m-*--cols m-+--cols) ()))))

(defthm m-*-dist-m-+-rows
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m1) (matrix->rows m3))
                (equal (matrix->cols m2) (matrix->cols m3)))
           (equal (m-*--rows m1 (m-+ m2 m3) r)
                  (m-+--rows (m-* m1 m2) (m-* m1 m3) r)))
  :hints (("Goal" :in-theory (e/d (m-*--rows m-+--rows) ()))))

(defthm m-*-dist-m-+
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m1) (matrix->rows m3))
                (equal (matrix->cols m2) (matrix->cols m3)))
           (equal (m-* m1 (m-+ m2 m3))
                  (m-+ (m-* m1 m2) (m-* m1 m3))))
  :hints (("Goal" :in-theory (e/d (m-* m-+) (m-*-dist-m-+-rows))
           :use (:instance m-*-dist-m-+-rows (r (matrix->rows m1))))))

;;;;;; Assoc of m-*
(define cross-prod-cols ((m2 matrix-p)
                      (m3 matrix-p)
                      (row natp)
                      (col natp))
  :returns (elems melems-p)
  (if (zp col)
      nil
    (cons (make-melem :r row :c col
                      :val (* (m-get m2 row (matrix->cols m2))
                              (m-get m3 (matrix->rows m3) col)))
          (cross-prod-cols m2 m3 row (1- col)))))


(define cross-prod-rows ((m2 matrix-p)
                      (m3 matrix-p)
                      (row natp))
  :returns (elems melems-p
                :hints (("Goal" :in-theory (e/d (melems-p-of-append) ()))))
  (b* (((matrix m2))
       ((matrix m3)))
    (if (zp row)
        nil
      (append (cross-prod-cols m2 m3 row m3.cols)
              (cross-prod-rows m2 m3 (1- row))))))

(define cross-prod-end ((m2 matrix-p)
                     (m3 matrix-p))
  :returns (mat matrix-p)
  (b* (((matrix m2))
       ((matrix m3)))
    (make-matrix :rows m2.rows :cols m3.cols :elems (cross-prod-rows m2 m3
                                                                     m2.rows)))
  ///
  (defthm cprod-end-rows-cols
    (and (equal (matrix->rows (cross-prod-end m2 m3)) (matrix->rows m2))
         (equal (matrix->cols (cross-prod-end m2 m3)) (matrix->cols m3)))))

(defthm m-get-aux-cross-prod-cols
  (equal (m-get-aux (cross-prod-cols m2 m3 row col) r c)
         (if (and (natp c) (natp r) (natp row) (natp col)
                  (equal row r) (<= c col))
             (* (m-get m2 r (matrix->cols m2))
                (m-get m3 (matrix->rows m3) c))
           0))
  :hints (("Goal" :in-theory (e/d (m-get-aux cross-prod-cols) ()))))

(defthm m-get-aux-append-cprod-cols-1
  (implies (not (equal r row))
           (equal (m-get-aux (append (cross-prod-cols m2 m3 row col) ls2) r c)
                  (m-get-aux ls2 r c)))
  :hints (("Goal" :in-theory (e/d (m-get-aux cross-prod-cols) ()))))

(defthm m-get-aux-append-cprod-cols-2
  (implies (and (natp c) (natp col))
           (equal (m-get-aux (append (cross-prod-cols m2 m3 row col) ls2) row c)
                  (if (<= c col)
                      (m-get-aux (cross-prod-cols m2 m3 row col) row c)
                    (m-get-aux ls2 row c))))
  :hints (("Goal" :in-theory (e/d (m-get-aux cross-prod-cols) ()))))

(defthm m-get-aux-cprod-rows
  (equal (m-get-aux (cross-prod-rows m2 m3 row) r c)
         (if (and (natp r) (natp c) (natp row) (<= r row))
             (* (m-get m2 r (matrix->cols m2))
                (m-get m3 (matrix->rows m3) c))
           0))
  :hints (("Goal" :in-theory (e/d (m-get-aux cross-prod-rows) ()))
          ("Subgoal *1/2.3" :use (:instance m-get-aux-append-cprod-cols-1
                                  (r r) (row row) (col (matrix->cols m3))
                                  (ls2 (cross-prod-rows m2 m3 (1- row))))
                            :in-theory (e/d () (m-get-aux-append-cprod-cols-1)))))

(defthmd m-get-cross-prod
  (equal (m-get (cross-prod-end m2 m3) r c)
         (if (and (natp r) (natp c) (<= r (matrix->rows m2)) (<= c (matrix->cols m3)))
             (* (m-get m2 r (matrix->cols m2))
                (m-get m3 (matrix->rows m3) c))
           0))
  :hints (("Goal" :in-theory (e/d (cross-prod-end) ())
                  :expand ((m-get (matrix (matrix->rows m2)
                                          (matrix->cols m3)
                                          (cross-prod-rows m2 m3 (matrix->rows m2)))
                                  r c)))))

(defthmd dprod-=-dprod-+-cprod
  (implies (and (natp r) (natp c) (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (dot-prod m2 m3 r c (matrix->cols m2))
                  (+ (dot-prod m2 m3 r c (1- (matrix->cols m2)))
                     (m-get (cross-prod-end m2 m3) r c))))
  :hints (("Goal" :expand ((dot-prod m2 m3 r c (matrix->cols m2)))
                  :use (m-get-cross-prod)
                  :in-theory (e/d (dot-prod) ()))))

(defthm m-*-get-special-cases
  (implies (or (zp (matrix->rows m1)) (zp (matrix->cols m1))
               (zp (matrix->rows m2)) (zp (matrix->cols m2)))
           (equal (m-get (m-* m1 m2) r c)
                  0))
  :hints (("Goal" :in-theory (e/d (m-* dot-prod m-get) ()))))

(defthm m-*-zp-col1-dot-prod-=-0
  (implies (zp (matrix->cols m2))
           (equal (dot-prod m1 (m-* m2 m3) r c size)
                  0))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthm get-sub-matrix-rows
  (implies (and (natp size2) (<= size2 (matrix->rows m3)) (natp r) (<= r size2))
           (equal (m-get (matrix size2 (matrix->cols m3) (matrix->elems m3)) r c)
                  (m-get m3 r c)))
  :hints (("Goal" :in-theory (e/d (m-get) ()))))

(defthm get-sub-matrix-cols
  (implies (and (natp size2) (natp c) (<= size2 (matrix->cols m)) (<= c size2))
           (equal (m-get (matrix (matrix->rows m) size2 (matrix->elems m)) r c)
                  (m-get m r c)))
  :hints (("Goal" :in-theory (e/d (m-get) ()))))


(defthm dot-prod-sub-matrix-cols
  (implies (and (natp size) (natp cols) (<= size cols) (<= cols (matrix->cols m2))
                (equal (matrix->cols m1) (matrix->rows m2)))
           (equal (dot-prod m1 (matrix (matrix->rows m2) cols (matrix->elems m2))
                            r size s)
                  (dot-prod m1 m2 r size s)))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthmd dot-prod-sub-matrix-col-row
  (implies (and (natp size) (natp size2) (<= size size2) (<= size2 (matrix->cols m2))
                (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (dot-prod m2 m3 r c size)
                  (dot-prod (matrix (matrix->rows m2) size2 (matrix->elems m2))
                            (matrix size2 (matrix->cols m3) (matrix->elems m3))
                            r c size)))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthm m-*-dot-prod-sub-matrix
  (implies (and (natp size) (natp size2) (<= size size2) (<= size2 (matrix->cols m2))
                (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (dot-prod (m-* m1
                                 (matrix (matrix->cols m1)
                                         size2
                                         (matrix->elems m2)))
                            (matrix size2
                                    (matrix->cols m3)
                                    (matrix->elems m3))
                            r c size)
                  (dot-prod (m-* m1 m2) m3 r c size)))
  :hints (("goal" :in-theory (e/d (dot-prod) (get-sub-matrix-cols)))
          ("Subgoal *1/5" :use ((:instance get-sub-matrix-cols
                                 (c size)
                                 (size2 size2)
                                 (m (m-* m1 m2))
                                 (r r))))
          ("Subgoal *1/2" :use ((:instance dot-prod-sub-matrix-cols
                                 (s (matrix->cols m1))
                                 (cols size2))))))

(defthmd get-m-*-=-get-m-*-+-cprod
  (implies (and (natp r) (natp c) (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (m-get (m-* m2 m3) r c)
                  (m-get (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                   :elems (matrix->elems m2))
                                      (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                   :elems (matrix->elems m3)))
                                 (cross-prod-end m2 m3)) r c)))
  :hints (("Goal" :in-theory (e/d (m-get-cross-prod dot-prod) ())
                  :expand ((dot-prod m2 m3 r c (matrix->cols m2)))
                  :use (:instance dot-prod-sub-matrix-col-row
                              (size (1- (matrix->cols m2)))
                             (size2 (1- (matrix->cols m2)))))))

(defthmd dprod-3-m-*-=-dprod-+-cprod
  (implies (and (natp r) (natp c) (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (dot-prod m1 (m-* m2 m3) r c s)
                  (dot-prod m1 (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                   :elems (matrix->elems m2))
                                      (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                   :elems (matrix->elems m3)))
                                    (cross-prod-end m2 m3)) r c s)))
  :hints (("Goal" :in-theory (e/d (dot-prod get-m-*-=-get-m-*-+-cprod) (m-*-get-dot-prod  m-+-get-sum)))))

(defthmd 3-m-*-=-m-*-+-cprod-cols
  (implies (and (natp r) (natp c) (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (m-*--cols m1 (m-* m2 m3) r c)
                  (m-*--cols m1 (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                   :elems (matrix->elems m2))
                                      (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                   :elems (matrix->elems m3)))
                                     (cross-prod-end m2 m3)) r c)))
  :hints (("Goal" :in-theory (e/d (m-*--cols dprod-3-m-*-=-dprod-+-cprod) ()))))

(defthmd 3-m-*-=-m-*-+-cprod-rows
  (implies (and (natp r) (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (m-*--rows m1 (m-* m2 m3) r)
                  (m-*--rows m1 (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                   :elems (matrix->elems m2))
                                      (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                   :elems (matrix->elems m3)))
                                     (cross-prod-end m2 m3)) r)))
  :hints (("Goal" :in-theory (e/d (m-*--rows 3-m-*-=-m-*-+-cprod-cols) ()))))

(defthmd 3-m-*-=-m-*-+-cprod
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (m-* m1 (m-* m2 m3))
                  (m-* m1 (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                   :elems (matrix->elems m2))
                                      (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                   :elems (matrix->elems m3)))
                               (cross-prod-end m2 m3)))))
  :hints (("Goal" :in-theory (e/d (3-m-*-=-m-*-+-cprod-rows) (m-*-dist-m-+))
                  :expand ((m-* m1 (m-* m2 m3))
                           (m-* m1
                                (m-+ (m-* (matrix (matrix->cols m1)
                                                  (+ -1 (matrix->cols m2))
                                                  (matrix->elems m2))
                                          (matrix (+ -1 (matrix->cols m2))
                                                  (matrix->cols m3)
                                                  (matrix->elems m3)))
                                     (cross-prod-end m2 m3)))))))

(defthm dot-prod-cross-prod
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m2) (matrix->rows m3))
                (natp r) (<= r (matrix->rows m1))
                (natp c) (<= c (matrix->cols m3)))
           (equal (dot-prod m1 (cross-prod-end m2 m3) r c s)
                  (* (m-get m3 (matrix->rows m3) c)
                     (dot-prod m1 m2 r (matrix->cols m2) s))))
  :hints (("Goal" :in-theory (e/d (dot-prod m-get-cross-prod) ()))))

;; (defthm dprod-right-=-dprod-+-cprod
;;   (implies (and (equal (matrix->cols m1) (matrix->rows m2))
;;                 (equal (matrix->cols m2) (matrix->rows m3)))
;;            (equal (dot-prod m1 (m-* m2 m3) r c (matrix->cols m1))
;;                   (+ (dot-prod m1 (m-* (matrix (matrix->cols m1)
;;                                                (+ -1 (matrix->cols m2))
;;                                                (matrix->elems m2))
;;                                        (matrix (+ -1 (matrix->cols m2))
;;                                                (matrix->cols m3)
;;                                                (matrix->elems m3)))
;;                                r c (matrix->cols m1))
;;                      (* (m-get m3 (matrix->cols m2) c)
;;                         (dot-prod m1 m2 r (matrix->cols m2) (matrix->cols m1)))))))

(defun assoc-induct-hint (m1 m2 m3 r c)
  (declare (irrelevant r c)
           (xargs :measure (matrix->cols m2)))
  (b* (((matrix m1))
       ((matrix m2))
       ((matrix m3)))
    (if (and (equal m1.cols m2.rows) (equal m2.cols m3.rows) (not (zp m2.cols)))
        (assoc-induct-hint m1 (make-matrix :rows m2.rows :cols (1- m2.cols) :elems m2.elems)
                           (make-matrix :rows (1- m3.rows) :cols m3.cols :elems m3.elems) r c)
      nil)))

(defthm assoc-*-get
  (equal (m-get (m-* (m-* m1 m2) m3) r c)
         (m-get (m-* m1 (m-* m2 m3)) r c))
  :hints (("Goal" :in-theory (e/d () ())
                  :induct (assoc-induct-hint m1 m2 m3 r c))
          ("Subgoal *1/2.3" :in-theory (e/d (m-*) ()))
          ("Subgoal *1/2.2" :in-theory (e/d (m-* m-get dot-prod) (m-*-zp-col1-dot-prod-=-0))
                            :use (:instance m-*-zp-col1-dot-prod-=-0
                                  (size (matrix->cols m1))))
          ("Subgoal *1/2.1" :in-theory (e/d (m-*) ()))
          ("Subgoal *1/1''" :in-theory (e/d (dot-prod) (m-*-dot-prod-sub-matrix))
           :use ((:instance m-*-dot-prod-sub-matrix
                  (size (1- (matrix->cols m2)))
                  (size2 (1- (matrix->cols m2))))
                 (:instance m-*-get-dot-prod
                            (m1 m1)
                            (m2 (m-* m2 m3)))
                 (:instance 3-m-*-=-m-*-+-cprod)
                 (:instance m-+-get-sum
                            (m1 (m-* m1 (m-* (matrix (matrix->cols m1)
                                                     (+ -1 (matrix->cols m2))
                                                     (matrix->elems m2))
                                             (matrix (+ -1 (matrix->cols m2))
                                                     (matrix->cols m3)
                                                     (matrix->elems m3)))))
                            (m2 (m-* m1 (cross-prod-end m2 m3))))
                 (:instance m-*-get-dot-prod
                            (m1 m1)
                            (m2 (cross-prod-end m2 m3)))
                 (:instance dot-prod-cross-prod (s (matrix->cols m1)))))))

(defthm assoc-*-dot-prod
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (dot-prod m1 (m-* m2 m3) r c (matrix->cols m1))
                  (dot-prod (m-* m1 m2) m3 r c (matrix->rows m3))))
  :hints (("Goal" :in-theory (e/d () (m-*-get-dot-prod))
                  :use ((:instance m-*-get-dot-prod
                         (m1 m1)
                         (m2 (m-* m2 m3)))
                        (:instance m-*-get-dot-prod (m1 (m-* m1 m2)) (m2 m3))))))

(defthm assoc-*-cols
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (m-*--cols (m-* m1 m2) m3 r c)
                  (m-*--cols m1 (m-* m2 m3) r c)))
  :hints (("Goal" :in-theory (e/d (m-*--cols) ()))))

(defthm assoc-*-rows
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (m-*--rows (m-* m1 m2) m3 r)
                  (m-*--rows m1 (m-* m2 m3) r)))
  :hints (("Goal" :in-theory (e/d (m-*--rows) ()))))

(defthm m-*-assoc
  (implies (and (equal (matrix->cols m1) (matrix->rows m2))
                (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (m-* (m-* m1 m2) m3)
                  (m-* m1 (m-* m2 m3))))
  :hints (("Goal" :in-theory (e/d (m-*) (assoc-*-rows))
                  :use (:instance assoc-*-rows
                        (r (matrix->rows m1))))))
