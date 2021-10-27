;; Theorems about row and col permutation matrices

(in-package "MAT")
(include-book "definitions")

;; (defthmd row-perm-m-get-aux-r1-1
;;   (implies (and (not (zp r1)) (not (zp r2)))
;;            (equal (m-get-aux (row-perm-aux m c1 r2) c1 c)
;;                   (m-get-aux m r2 c)))
;;   :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

;; (defthmd row-perm-m-get-aux-r2-1
;;   (implies (and (not (zp c1)) (not (zp r2)))
;;            (equal (m-get-aux (row-perm-aux m c1 r2) r2 c)
;;                   (m-get-aux m c1 c)))
;;   :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

;; (defthmd row-perm-m-get-aux-r1-2
;;   (implies (or (equal c1 0) (equal r2 0))
;;            (equal (m-get-aux (row-perm-aux m c1 r2) c1 c)
;;                   0))
;;   :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

;; (defthmd row-perm-m-get-aux-r2-2
;;   (implies (or (equal c1 0) (equal r2 0))
;;            (equal (m-get-aux (row-perm-aux m c1 r2) r2 c)
;;                   0))
;;   :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

;; (defthm row-perm-m-get-aux-r
;;   (implies (and (not (equal (nfix r) (nfix c1)))
;;                 (not (equal (nfix r) (nfix r2)))
;;                 (not (zp r)))
;;            (equal (m-get-aux (row-perm-aux m c1 r2) r c)
;;                   (m-get-aux m r c)))
;;   :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

;; (defthm row-perm-m-get
;;   (equal (m-get (row-perm m c1 r2) r c)
;;          (cond ((or (zp r) (< (matrix->rows m) r)) 0)
;;                ((equal r c1) (m-get m r2 c))
;;                ((equal r r2) (m-get m c1 c))
;;                (t            (m-get m r  c))))
;;   :hints (("Goal" :in-theory (e/d (row-perm
;;                                    m-get
;;                                    row-perm-m-get-aux-r
;;                                    row-perm-m-get-aux-r2-2
;;                                    row-perm-m-get-aux-r2-1
;;                                    row-perm-m-get-aux-r1-2
;;                                    row-perm-m-get-aux-r1-1) ()))))

(defthm row-perm-m-get-aux-0-1
  (not (m-get-aux (row-perm-aux m r1 0) r1 c))
  :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

(defthm row-perm-m-get-aux-0-2
  (not (m-get-aux (row-perm-aux m 0 r2) r2 c))
  :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

(defthm row-perm-get-aux-prelim-1
  (implies (and (not (zp r1)) (not (zp r2)))
           (equal (melem->val (m-get-aux (row-perm-aux m r1 r2) r1 c))
                  (melem->val (m-get-aux m r2 c))))
  :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

(defthm row-perm-get-aux-prelim-2
  (implies (and (not (zp r1)) (not (zp r2)))
           (equal (melem->val (m-get-aux (row-perm-aux m r1 r2) r2 c))
                  (melem->val (m-get-aux m r1 c))))
  :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

(defthm row-perm-m-get-aux
  (equal (melem->val (m-get-aux (row-perm-aux m r1 r2) r c))
         (cond ((or (zp r) (zp c)) 0)
               ((and (equal r1 r) (zp r2)) 0)
               ((equal r1 r) (melem->val (m-get-aux m r2 c)))
               ((and (equal r2 r) (zp r1)) 0)
               ((equal r2 r) (melem->val (m-get-aux m r1 c)))
               (t (melem->val (m-get-aux m r c)))))
  :hints (("Goal" :in-theory (e/d (m-get-aux row-perm-aux) ()))))

(defthm row-perm-m-get
  (equal (m-get (row-perm m r1 r2) r c)
         (cond ((equal r r1) (m-get m r2 c))
               ((equal r r2) (m-get m r1 c))
               (t (m-get m r c))))
  :hints (("Goal" :in-theory (e/d (m-get row-perm) ()))))



(defthmd col-perm-m-get-aux-c1-1
  (implies (and (not (zp c1)) (not (zp c2)))
           (equal (m-get-aux (col-perm-aux m c1 c2) r c1)
                  (m-get-aux m r c2)))
  :hints (("Goal" :in-theory (e/d (m-get-aux col-perm-aux) ()))))

(defthmd col-perm-m-get-aux-c2-1
  (implies (and (not (zp c1)) (not (zp c2)))
           (equal (m-get-aux (col-perm-aux m c1 c2) r c2)
                  (m-get-aux m r c1)))
  :hints (("Goal" :in-theory (e/d (m-get-aux col-perm-aux) ()))))

(defthmd col-perm-m-get-aux-c1-2
  (implies (or (equal c1 0) (equal c2 0))
           (equal (m-get-aux (col-perm-aux m c1 c2) r c1)
                  0))
  :hints (("Goal" :in-theory (e/d (m-get-aux col-perm-aux) ()))))

(defthmd col-perm-m-get-aux-c2-2
  (implies (or (equal c1 0) (equal c2 0))
           (equal (m-get-aux (col-perm-aux m c1 c2) r c2)
                  0))
  :hints (("Goal" :in-theory (e/d (m-get-aux col-perm-aux) ()))))

(defthm col-perm-m-get-aux-c
  (implies (and (not (equal (nfix c) (nfix c1)))
                (not (equal (nfix c) (nfix c2)))
                (not (zp c)))
           (equal (m-get-aux (col-perm-aux m c1 c2) r c)
                  (m-get-aux m r c)))
  :hints (("Goal" :in-theory (e/d (m-get-aux col-perm-aux) ()))))

(defthm col-perm-m-get
  (equal (m-get (col-perm m c1 c2) r c)
         (cond ((or (zp c) (< (matrix->cols m) c)) 0)
               ((equal c c1) (m-get m r c2))
               ((equal c c2) (m-get m r c1))
               (t            (m-get m r c))))
  :hints (("Goal" :in-theory (e/d (col-perm
                                   m-get
                                   col-perm-m-get-aux-c
                                   col-perm-m-get-aux-c2-2
                                   col-perm-m-get-aux-c2-1
                                   col-perm-m-get-aux-c1-2
                                   col-perm-m-get-aux-c1-1) ()))))

(defthm perm-iden-dot-prod-1
  (implies (and (equal (matrix->rows m) n) (not (zp r1)) (not (zp r2))
                (<= r1 n) (<= r2 n) (<= size r2))
           (equal (dot-prod (row-perm (iden n) r1 r2)
                            m r1 col size)
                  (m-get m r2 col)))
  :hints (("Goal" :in-theory (e/d (dot-prod) ()))))


                  (cond ((and (<= size r2) (equal row r1)) (m-get m r2 col))
                        ((and (<= size r1) (equal row r2)) (m-get m r1 col))
                        ((<= size row) (m-get m row col))
                        (t 0))


(defthm m-=-perm-iden-col
  (implies (and (equal (matrix->rows m) n) (not (zp r1)) (not (zp r2))
                (<= r1 n) (<= r2 n) (<= c col) (natp col))
           (m-=--cols (m-*--cols (row-perm (iden n) r1 r2) m row col)
                      (row-perm m r1 r2) row c))
  :hints (("Goal" :in-theory (e/d (m-=--cols m-*--cols) ()))))

(defthm m-=-perm-iden
  (implies (and (equal (matrix->rows m) n) (not (zp r1)) (not (zp r2))
                (<= r1 n) (<= r2 n))
           (m-= (m-* (row-perm (iden n) r1 r2) m)
                (row-perm m r1 r2))))
