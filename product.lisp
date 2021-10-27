;; Matrix product theorems

(in-package "MAT")

(include-book "definitions")
(include-book "equality")

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (e/d (m-=--rows m-=--cols mult-p) ())))

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
             nil
           (if (equal r c)
               (make-melem :r r :c r :val 1)
             nil)))
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
  (implies (and (mult-p m1 m2)
                (not (zp r))
                (not (zp c))
                (case-split (not (zp cols))))
           (equal (m-get-aux (m-*--cols m1 m2 row cols) r c)
                  (if (and (<= c cols) (equal r row))
                      (make-melem :r r :c c
                                  :val (dot-prod m1 m2 r c (matrix->cols m1)))
                    nil)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-*--cols) ()))))

(defthm m-*-get-dot-prod-rows
  (implies (and (mult-p m1 m2)
                (not (zp r))
                (not (zp c))
                (not (zp row)))
           (equal (m-get-aux (m-*--rows m1 m2 row) r c)
                  (if (<= r row)
                      (m-get-aux (m-*--cols m1 m2 r (matrix->cols m2)) r c)
                    nil)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-*--rows m-*--cols) (mult-p)))))

(defthm m-*-get-dot-prod
  (implies (mult-p m1 m2)
           (equal (m-get (m-* m1 m2) r c)
                  (dot-prod m1 m2 r c (matrix->cols m1))))
  :hints (("Goal" :in-theory (e/d (m-get m-*) (mult-p)))))

(defthm m-*-get-special-cases
  (implies (or (zp (matrix->rows m1)) (zp (matrix->cols m1))
               (zp (matrix->rows m2)) (zp (matrix->cols m2)))
           (equal (m-get (m-* m1 m2) r c)
                  0))
  :hints (("Goal" :in-theory (e/d (m-* dot-prod m-get) ()))))

(defthm m-*-iden-right-cols
  (m-=--cols (m-* m1 (iden (matrix->cols m1))) m1 r c)
  :hints (("Goal" :in-theory (e/d (dot-prod-iden-right) ()))))

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
  (implies (mult-p m1 m2)
           (equal (dot-prod (transpose m2) (transpose m1) r c size)
                  (dot-prod (matrix-fix m1) (matrix-fix m2) c r size)))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthm trans-prod-prod-trans-cols
  (implies (and (mult-p m1 m2) (matrix-p m1) (matrix-p m2))
           (m-=--cols (transpose (m-* m1 m2))
                      (m-* (transpose m2) (transpose m1)) r c)))

(defthm trans-prod-prod-trans-rows
  (implies (and (mult-p m1 m2) (matrix-p m1) (matrix-p m2))
           (m-=--rows (transpose (m-* m1 m2))
                      (m-* (transpose m2) (transpose m1)) r)))


(defthm trans-m-*-m-*-trans
  (implies (and (mult-p m1 m2) (matrix-p m1) (matrix-p m2))
           (m-= (transpose (m-* m1 m2))
                (m-* (transpose m2) (transpose m1))))
  :hints (("Goal" :in-theory (e/d (m-=) ()))))


;; Product distributes over sum
(local (include-book "sum"))

(defthm m-*-dist-m-+-dot-prod
  (implies (and (mult-p m1 m2) (mult-p m1 m3) (summable-p m2 m3))
         (equal (dot-prod m1 (m-+ m2 m3) r c s)
                (+ (dot-prod m1 m2 r c s)
                   (dot-prod m1 m3 r c s))))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthm m-*-dist-m-+-get
  (implies (and (mult-p m1 m2) (mult-p m1 m3) (summable-p m2 m3))
           (equal (m-get (m-* m1 (m-+ m2 m3)) r c)
                  (+ (m-get (m-* m1 m2) r c)
                     (m-get (m-* m1 m3) r c))))
  :hints (("Goal" :use ((:instance m-+-rows-cols
                         (m1 m2)
                         (m2 m3))))))

(defthm m-*-dist-m-+-cols
  (implies (and (mult-p m1 m2) (mult-p m1 m3) (summable-p m2 m3))
           (equal (m-*--cols m1 (m-+ m2 m3) r c)
                  (m-+--cols (m-* m1 m2) (m-* m1 m3) r c)))
  :hints (("Goal" :in-theory (e/d (m-*--cols m-+--cols summable-p) ()))))

(defthm m-*-dist-m-+-rows
  (implies (and (mult-p m1 m2) (mult-p m1 m3) (summable-p m2 m3))
           (equal (m-*--rows m1 (m-+ m2 m3) r)
                  (m-+--rows (m-* m1 m2) (m-* m1 m3) r)))
  :hints (("Goal" :in-theory (e/d (m-*--rows m-+--rows summable-p) ()))))

(defthm m-*-dist-m-+
  (implies (and (mult-p m1 m2) (mult-p m1 m3) (summable-p m2 m3))
           (equal (m-* m1 (m-+ m2 m3))
                  (m-+ (m-* m1 m2) (m-* m1 m3))))
  :hints (("Goal" :in-theory (e/d (m-* m-+ summable-p) (m-*-dist-m-+-rows))
                  :use (:instance m-*-dist-m-+-rows (r (matrix->rows m1))))))

;;;;;; Assoc of m-*
(define cprod-cols ((m2 matrix-p)
                    (m3 matrix-p)
                    (row natp)
                    (col natp))
  :returns (elems melems-p)
  (if (or (zp col) (zp row))
      nil
    (cons (make-melem :r row :c col
                      :val (* (m-get m2 row (matrix->cols m2))
                              (m-get m3 (matrix->rows m3) col)))
          (cprod-cols m2 m3 row (1- col)))))


(define cprod-rows ((m2 matrix-p)
                    (m3 matrix-p)
                    (row natp))
  :returns (elems melems-p
                  :hints (("Goal" :in-theory (e/d (melems-p-of-append) ()))))
  (b* (((matrix m2))
       ((matrix m3)))
    (if (zp row)
        nil
      (append (cprod-cols m2 m3 row m3.cols)
              (cprod-rows m2 m3 (1- row))))))

(define cprod-end ((m2 matrix-p)
                   (m3 matrix-p))
  :returns (mat matrix-p)
  (b* (((matrix m2))
       ((matrix m3)))
    (make-matrix :rows m2.rows :cols m3.cols :elems (cprod-rows m2 m3
                                                                m2.rows)))
  ///
  (defthm cprod-end-rows-cols
    (and (equal (matrix->rows (cprod-end m2 m3)) (matrix->rows m2))
         (equal (matrix->cols (cprod-end m2 m3)) (matrix->cols m3)))))

(defthm m-get-aux-cprod-cols
  (equal (m-get-aux (cprod-cols m2 m3 row col) r c)
         (if (and (not (zp c)) (not (zp r)) (not (zp row)) (not (zp col))
                  (equal row r) (<= c col))
             (make-melem :r r :c c :val (* (m-get m2 r (matrix->cols m2))
                                           (m-get m3 (matrix->rows m3) c)))
           nil))
  :hints (("Goal" :in-theory (e/d (m-get-aux cprod-cols) ()))))


(defthm m-get-aux-cprod-rows
  (equal (m-get-aux (cprod-rows m2 m3 row) r c)
         (if (or (zp r) (zp c) (zp row) (< row r))
             nil
           (m-get-aux (cprod-cols m2 m3 r (matrix->cols m3)) r c)))
  :hints (("Goal" :in-theory (e/d (m-get-aux cprod-rows) ()))))

(defthmd m-get-cross-prod
  (equal (m-get (cprod-end m2 m3) r c)
         (if (or (zp r) (zp c) (< (matrix->rows m2) r) (< (matrix->cols m3) c))
             0
           (* (m-get m2 r (matrix->cols m2))
              (m-get m3 (matrix->rows m3) c))))
  :hints (("Goal" :in-theory (e/d (cprod-end) ())
                  :expand ((m-get (matrix (matrix->rows m2)
                                          (matrix->cols m3)
                                          (cprod-rows m2 m3 (matrix->rows m2)))
                                  r c)))))

(defthmd dprod-=-dprod-+-cprod
  (implies (and (natp r) (natp c) (equal (matrix->cols m2) (matrix->rows m3)))
           (equal (dot-prod m2 m3 r c (matrix->cols m2))
                  (+ (dot-prod m2 m3 r c (1- (matrix->cols m2)))
                     (m-get (cprod-end m2 m3) r c))))
  :hints (("Goal" :expand ((dot-prod m2 m3 r c (matrix->cols m2)))
                  :use (m-get-cross-prod)
                  :in-theory (e/d (dot-prod) ()))))

(defthm get-sub-matrix-rows
  (implies (and (natp size2) (<= size2 (matrix->rows m3)) (natp r))
           (equal (m-get (matrix size2 (matrix->cols m3) (matrix->elems m3)) r c)
                  (if (<= r size2)
                      (m-get m3 r c)
                    0)))
  :hints (("Goal" :in-theory (e/d (m-get) ()))))

(defthm get-sub-matrix-cols
  (implies (and (natp size2) (natp c) (<= size2 (matrix->cols m)))
           (equal (m-get (matrix (matrix->rows m) size2 (matrix->elems m)) r c)
                  (if (<= c size2)
                      (m-get m r c)
                    0)))
  :hints (("Goal" :in-theory (e/d (m-get) ()))))

(defthm dot-prod-sub-matrix-cols
  (implies (and (natp size) (natp cols) (<= size cols) (<= cols (matrix->cols m2))
                (mult-p m1 m2))
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
          ("Subgoal *1/2" :use ((:instance dot-prod-sub-matrix-cols
                                 (s (matrix->cols m1))
                                 (cols size2))))))

(defthmd get-m-*-=-get-m-*-+-cprod
  (implies (and (natp r) (natp c) (mult-p m2 m3))
           (equal (m-get (m-* m2 m3) r c)
                  (m-get (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                :elems (matrix->elems m2))
                                   (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                :elems (matrix->elems m3)))
                              (cprod-end m2 m3)) r c)))
  :hints (("Goal" :in-theory (e/d (m-get-cross-prod dot-prod summable-p) ())
                  :expand ((dot-prod m2 m3 r c (matrix->cols m2)))
                  :use (:instance dot-prod-sub-matrix-col-row
                        (size (1- (matrix->cols m2)))
                        (size2 (1- (matrix->cols m2)))))))

(defthmd dprod-3-m-*-=-dprod-+-cprod
  (implies (and (natp r) (natp c) (mult-p m2 m3) (mult-p m1 m2))
           (equal (dot-prod m1 (m-* m2 m3) r c s)
                  (dot-prod m1 (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                      :elems (matrix->elems m2))
                                         (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                      :elems (matrix->elems m3)))
                                    (cprod-end m2 m3)) r c s)))
  :hints (("Goal" :in-theory (e/d (dot-prod get-m-*-=-get-m-*-+-cprod) (m-*-get-dot-prod  m-+-get-sum)))))

(defthm summable-p-parts-lemma
  (implies (and (mult-p m2 m3) (mult-p m1 m2))
           (summable-p (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                         :elems (matrix->elems m2))
                            (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                         :elems (matrix->elems m3)))
                       (cprod-end m2 m3)))
  :hints (("Goal" :in-theory (e/d (summable-p) ()))))


(defthmd 3-m-*-=-m-*-+-cprod-cols
  (implies (and (natp r) (natp c) (mult-p m2 m3) (mult-p m1 m2))
           (equal (m-*--cols m1 (m-* m2 m3) r c)
                  (m-*--cols m1 (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                   :elems (matrix->elems m2))
                                      (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                   :elems (matrix->elems m3)))
                                     (cprod-end m2 m3)) r c)))
  :hints (("Goal" :in-theory (e/d (m-*--cols dprod-3-m-*-=-dprod-+-cprod) ()))
          ("Subgoal *1/2" :use (summable-p-parts-lemma)
                          :in-theory (e/d (m-*--cols m-+--cols) ()))))

(defthmd 3-m-*-=-m-*-+-cprod-rows
  (implies (and (natp r) (mult-p m2 m3) (mult-p m1 m2))
           (equal (m-*--rows m1 (m-* m2 m3) r)
                  (m-*--rows m1 (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                   :elems (matrix->elems m2))
                                      (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                   :elems (matrix->elems m3)))
                                     (cprod-end m2 m3)) r)))
  :hints (("Goal" :in-theory (e/d (m-*--rows 3-m-*-=-m-*-+-cprod-cols summable-p) ()))
          ("Subgoal *1/2" :use (summable-p-parts-lemma)
                          :in-theory (e/d (m-+--rows m-*--rows) ()))
          ("Subgoal *1/1" :use (summable-p-parts-lemma)
                          :expand ((m-+--rows (m-* m1
                                                   (m-* (matrix (matrix->cols m1)
                                                                (+ -1 (matrix->cols m2))
                                                                (matrix->elems m2))
                                                        (matrix (+ -1 (matrix->cols m2))
                                                                (matrix->cols m3)
                                                                (matrix->elems m3))))
                                              (m-* m1 (cprod-end m2 m3))
                                              r)))))

(defthmd 3-m-*-=-m-*-+-cprod
  (implies (and (mult-p m1 m2) (mult-p m2 m3))
           (equal (m-* m1 (m-* m2 m3))
                  (m-* m1 (m-+ (m-* (make-matrix :rows (matrix->rows m2) :cols (1- (matrix->cols m2))
                                                   :elems (matrix->elems m2))
                                      (make-matrix :rows (1- (matrix->rows m3)) :cols (matrix->cols m3)
                                                   :elems (matrix->elems m3)))
                               (cprod-end m2 m3)))))
  :hints (("Goal" :in-theory (e/d (3-m-*-=-m-*-+-cprod-rows summable-p) (m-*-dist-m-+))
                  :expand ((m-* m1 (m-* m2 m3))
                           (m-* m1
                                (m-+ (m-* (matrix (matrix->cols m1)
                                                  (+ -1 (matrix->cols m2))
                                                  (matrix->elems m2))
                                          (matrix (+ -1 (matrix->cols m2))
                                                  (matrix->cols m3)
                                                  (matrix->elems m3)))
                                     (cprod-end m2 m3)))))))

(defthm dot-prod-cprod
  (implies (and (mult-p m1 m2) (mult-p m2 m3)
                (natp r) (<= r (matrix->rows m1))
                (natp c) (<= c (matrix->cols m3)))
           (equal (dot-prod m1 (cprod-end m2 m3) r c s)
                  (* (m-get m3 (matrix->rows m3) c)
                     (dot-prod m1 m2 r (matrix->cols m2) s))))
  :hints (("Goal" :in-theory (e/d (dot-prod m-get-cross-prod) ()))))

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

(defthm zp-m2-col-dprod-0
  (implies (and (zp (matrix->cols m2)) (mult-p m1 m2) (mult-p m2 m3))
           (equal (dot-prod m1 (m-* m2 m3) r c s) 0))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))

(defthm assoc-*-get
  (implies (and (mult-p m1 m2) (mult-p m2 m3))
           (equal (m-get (m-* (m-* m1 m2) m3) r c)
                  (m-get (m-* m1 (m-* m2 m3)) r c)))
  :hints (("Goal" :in-theory (e/d () (m-*-get-dot-prod))
                  :induct (assoc-induct-hint m1 m2 m3 r c))
          ("Subgoal *1/2" :in-theory (e/d (m-*-get-dot-prod) ()))
          ("Subgoal *1/1" :in-theory (e/d (3-m-*-=-m-*-+-cprod) (m-*-dist-m-+))
                          :expand ((dot-prod (m-* m1 m2)
                                             m3 r c (matrix->cols m2)))
                          :use ((:instance m-*-dist-m-+
                                 (m1 m1)
                                 (m2 (m-* (matrix (matrix->cols m1)
                                                  (+ -1 (matrix->cols m2))
                                                  (matrix->elems m2))
                                          (matrix (+ -1 (matrix->cols m2))
                                                  (matrix->cols m3)
                                                  (matrix->elems m3))))
                                 (m3 (cprod-end m2 m3)))
                                summable-p-parts-lemma
                                (:instance dot-prod-cprod
                                           (s (matrix->cols m1)))))))

(defthm assoc-*-dot-prod
  (implies (and (mult-p m1 m2) (mult-p m2 m3))
           (equal (dot-prod m1 (m-* m2 m3) r c (matrix->cols m1))
                  (dot-prod (m-* m1 m2) m3 r c (matrix->rows m3))))
  :hints (("Goal" :in-theory (e/d () (m-*-get-dot-prod))
                  :use ((:instance m-*-get-dot-prod
                         (m1 m1)
                         (m2 (m-* m2 m3)))
                        (:instance m-*-get-dot-prod (m1 (m-* m1 m2)) (m2 m3))))))

(defthm assoc-*-cols
  (implies (and (mult-p m1 m2) (mult-p m2 m3))
           (equal (m-*--cols (m-* m1 m2) m3 r c)
                  (m-*--cols m1 (m-* m2 m3) r c)))
  :hints (("Goal" :in-theory (e/d (m-*--cols) ()))))

(defthm assoc-*-rows
  (implies (and (mult-p m1 m2) (mult-p m2 m3))
           (equal (m-*--rows (m-* m1 m2) m3 r)
                  (m-*--rows m1 (m-* m2 m3) r)))
  :hints (("Goal" :in-theory (e/d (m-*--rows) ()))))

(defthm m-*-assoc
  (implies (and (mult-p m1 m2) (mult-p m2 m3))
           (equal (m-* (m-* m1 m2) m3)
                  (m-* m1 (m-* m2 m3))))
  :hints (("Goal" :in-theory (e/d (m-*) (assoc-*-rows))
                  :use (:instance assoc-*-rows
                        (r (matrix->rows m1))))))
