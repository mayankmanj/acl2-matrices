;;; matrix summation theorems

(in-package "MAT")

(include-book "definitions")
(include-book "equality")
(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (e/d (m-=--rows m-=--cols) (m-=))))

(defcong m-= equal (m-+--cols m1 m2 row cols) 1
  :hints (("Goal" :in-theory (e/d (m-+--cols) ()))))

(defcong m-= equal (m-+--cols m1 m2 row cols) 2
  :hints (("Goal" :in-theory (e/d (m-+--cols) ()))))

(defcong m-= equal (m-+--rows m1 m2 rows) 1
  :hints (("Goal" :in-theory (e/d (m-+--rows) ()))))

(defcong m-= equal (m-+--rows m1 m2 rows) 2
  :hints (("Goal" :in-theory (e/d (m-+--rows) ()))))

(defcong m-= equal (m-+ m1 m2) 1
  :hints (("Goal" :in-theory (e/d (m-+) ()))))

(defcong m-= equal (m-+ m1 m2) 2
  :hints (("Goal" :in-theory (e/d (m-+) ()))))

(defthm m-+-get-cols
  (implies (<= c (nfix cols))
           (equal (m-get-aux (m-+--cols m1 m2 r cols) r c)
                  (+ (m-get m1 r c) (m-get m2 r c))))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--cols) ()))))

(defthm m-+-row-append-get-aux-1
  (implies (<= c (nfix col))
           (equal (m-get-aux (append (m-+--cols m1 m2 row col) ls) row c)
                  (m-get-aux (m-+--cols m1 m2 row col) row c)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--cols) ()))))

(defthm m-+-row-append-get-aux-2
  (implies (or (not (equal row r)) (< col c))
           (equal (m-get-aux (append (m-+--cols m1 m2 row col) ls) r c)
                  (m-get-aux ls r c)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--cols) ()))))

(defthm m-+-row-get-aux-1
  (implies (and (<= (nfix r) (nfix row)) (<= c (matrix->cols m1))
                (equal (matrix->cols m1) (matrix->cols m2)))
           (equal (m-get-aux (m-+--rows m1 m2 row) r c)
                  (m-get-aux (m-+--cols m1 m2 r (matrix->cols m1)) r c)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--rows) ()))
          ("Subgoal *1/2" :cases ((< r row)))))

(defthm m-+-row-get-row-out-of-bounds
  (implies (and (natp r) (natp row) (< row r))
           (equal (m-get-aux (m-+--rows m1 m2 row) r c) 0))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--rows) ()))))

(defthm m-+-row-get-col-out-of-bounds
  (implies (< (matrix->cols m1) c)
           (equal (m-get-aux (m-+--rows m1 m2 row) r c)
                  0))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--rows) ()))))

(defthm m-+-get-rows
  (implies (and (natp r) (natp rows) (<= r rows) (natp c)
                (equal (matrix->cols m1) (matrix->cols m2)))
           (equal (m-get-aux (m-+--rows m1 m2 rows) r c)
                  (+ (m-get m1 r c) (m-get m2 r c))))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--rows) ()))
          ("Subgoal *1/5" :cases ((equal r rows)))
          ("Subgoal *1/5.1" :cases ((<= c (matrix->cols m1))))
          ("Subgoal *1/4" :cases ((<= c (matrix->cols m1))))))

(defthm m-+-get-sum
  (implies (and (equal (matrix->rows m1) (matrix->rows m2))
                (equal (matrix->cols m1) (matrix->cols m2)))
           (equal (m-get (m-+ m1 m2) r c)
                  (+ (m-get m1 r c) (m-get m2 r c))))
  :hints (("Goal''" :in-theory (e/d () ())
                  :expand ((m-get (m-+ m1 m2) r c)))
          ("Goal'''" :expand (m-+ m1 m2))))

(defthm m-+-iden-right-cols
  (m-=--cols (m-+ m1 (zeros-r-c (matrix->rows m1) (matrix->cols m1))) m1 r c)
  :hints (("Goal" :in-theory (e/d () ()))))

(defthm m-+-iden-right-rows
  (m-=--rows (m-+ m1 (zeros-r-c (matrix->rows m1) (matrix->cols m1))) m1 r))

(defthm m-+-iden-right
  (m-= (m-+ m1 (zeros-r-c (matrix->rows m1) (matrix->cols m1))) m1)
  :hints (("Goal" :in-theory (e/d (m-=) ()))))

(defthm m-+-iden-left-cols
  (m-=--cols (m-+ (zeros-r-c (matrix->rows m1) (matrix->cols m1)) m1) m1 r c))

(defthm m-+-iden-left-rows
  (m-=--rows (m-+ (zeros-r-c (matrix->rows m1) (matrix->cols m1)) m1) m1 r))

(defthm m-+-iden-left
  (m-= (m-+ (zeros-r-c (matrix->rows m1) (matrix->cols m1)) m1) m1)
  :hints (("Goal" :in-theory (e/d (m-=) ()))))

(defthm m-+-dim-not-equal
  (implies (or (not (equal (matrix->rows m1) (matrix->rows m2)))
               (not (equal (matrix->cols m1) (matrix->cols m2))))
           (equal (m-get (m-+ m1 m2) r c) 0))
  :hints (("Goal" :in-theory (e/d (m-+) ()))))

(defthm m-+-assoc-cols
  (implies (and (equal (matrix->rows m1) (matrix->rows m2))
                (equal (matrix->rows m2) (matrix->rows m3))
                (equal (matrix->cols m1) (matrix->cols m2))
                (equal (matrix->cols m2) (matrix->cols m3)))
           (equal (m-+--cols (m-+ m1 m2) m3 r c)
                  (m-+--cols m1 (m-+ m2 m3) r c)))
  :hints (("Goal" :in-theory (e/d (m-+--cols) (m-+-get-sum)))
          ("Subgoal *1/2" :use ((:instance m-+-get-sum)
                                (:instance m-+-get-sum (m1 m2) (m2 m3))))))

(defthm m-+-assoc-rows
  (implies (and (equal (matrix->rows m1) (matrix->rows m2))
                (equal (matrix->rows m2) (matrix->rows m3))
                (equal (matrix->cols m1) (matrix->cols m2))
                (equal (matrix->cols m2) (matrix->cols m3)))
           (equal (m-+--rows (m-+ m1 m2) m3 r)
                  (m-+--rows m1 (m-+ m2 m3) r)))
  :hints (("Goal" :in-theory (e/d (m-+--rows) ()))))

(defthm m-+-assoc
  (equal (m-+ (m-+ m1 m2) m3)
         (m-+ m1 (m-+ m2 m3)))
  :hints (("Goal" :in-theory (e/d (m-+ m-+--rows) ()))
          ("Subgoal 7" :in-theory (e/d (m-+) (m-+-assoc-rows))
                       :use (:instance m-+-assoc-rows (r (matrix->rows m1))))))

(defthmd m-+-comm-cols
  (implies (and (equal (matrix->rows m1) (matrix->rows m2))
                (equal (matrix->rows m2) (matrix->rows m3))
                (equal (matrix->cols m1) (matrix->cols m2))
                (equal (matrix->cols m2) (matrix->cols m3)))
          (equal (m-+--cols m1 m2 r c)
                 (m-+--cols m2 m1 r c)))
  :hints (("Goal" :in-theory (e/d (m-+--cols) ()))))

(defthmd m-+-comm-rows
  (implies (and (equal (matrix->rows m1) (matrix->rows m2))
                (equal (matrix->rows m2) (matrix->rows m3))
                (equal (matrix->cols m1) (matrix->cols m2))
                (equal (matrix->cols m2) (matrix->cols m3)))
           (equal (m-+--rows m1 m2 r)
                  (m-+--rows m2 m1 r)))
  :hints (("Goal" :in-theory (e/d (m-+--rows m-+-comm-cols) ()))))

(defthmd m-+-comm
  (equal (m-+ m1 m2)
         (m-+ m2 m1))
  :hints (("Goal" :expand ((m-+ m1 m2) (m-+ m2 m1))
                  :in-theory (e/d (m-+-comm-rows) ()))))
