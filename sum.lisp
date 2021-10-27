;;; matrix summation theorems

(in-package "MAT")

(include-book "definitions")
(include-book "equality")
(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (e/d (m-=--rows m-=--cols summable-p) (m-=))))

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
  (implies (and (summable-p m1 m2)
                (not (zp cols))
                (not (zp r))
                (not (zp row))
                (not (zp c)))
           (equal (m-get-aux (m-+--cols m1 m2 row cols) r c)
                  (if (and (<= c cols) (equal r row))
                      (make-melem :r (nfix r) :c c :val (+ (m-get m1 r c)
                                                           (m-get m2 r c)))
                    nil)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--cols) ()))))

(defthm m-+-row-get-aux-1
  (implies (and (summable-p m1 m2)
                (not (zp r))
                (not (zp row))
                (not (zp c)))
           (equal (m-get-aux (m-+--rows m1 m2 row) r c)
                  (if (<= r row)
                      (m-get-aux (m-+--cols m1 m2 r (matrix->cols m1)) r c)
                    nil)))
  :hints (("Goal" :in-theory (e/d (m-get-aux m-+--rows) (summable-p)))
          ("Subgoal *1/8" :in-theory (e/d (m-+--cols m-get-aux) (m-+-get-cols))
                          :use ((:instance m-+-get-cols
                                           (row 1)
                                           (cols (matrix->cols m1)))))
          ("Subgoal *1/6" :cases ((equal r 1))
                          :in-theory (e/d (m-+--cols) ())
                          :use ((:instance m-+-get-cols
                                           (row 1)
                                           (cols (matrix->cols m1)))))
          ("Subgoal *1/3" :use ((:instance m-+-get-cols
                                           (cols (matrix->cols m1))))
                          :in-theory (e/d (m-+--cols) ()))
          ("Subgoal *1/2" :use ((:instance m-+-get-cols
                                           (cols (matrix->cols m1))))
                          :in-theory (e/d (m-+--cols m-get-aux) ()))))

(defthm m-+-get-sum
  (implies (summable-p m1 m2)
           (equal (m-get (m-+ m1 m2) r c)
                  (+ (m-get m1 r c) (m-get m2 r c))))
  :hints (("Goal" :in-theory (e/d (m-get m-+) ()))))

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

(defthm m-+-assoc-cols
  (implies (and (summable-p m1 m2)
                (summable-p m2 m3))
           (equal (m-+--cols (m-+ m1 m2) m3 r c)
                  (m-+--cols m1 (m-+ m2 m3) r c)))
  :hints (("Goal" :in-theory (e/d (m-+--cols) ()))))

(defthm m-+-assoc-rows
  (implies (and (summable-p m1 m2)
                (summable-p m2 m3))
           (equal (m-+--rows (m-+ m1 m2) m3 r)
                  (m-+--rows m1 (m-+ m2 m3) r)))
  :hints (("Goal" :in-theory (e/d (m-+--rows) ()))))

(defthm m-+-assoc
  (equal (m-+ (m-+ m1 m2) m3)
         (m-+ m1 (m-+ m2 m3)))
  :hints (("Goal" :cases ((and (summable-p m1 m2)
                               (summable-p m2 m3))))
          ("Subgoal 2" :in-theory (e/d (m-+--rows m-+) ()))
          ("Subgoal 1" :use ((:instance m-+-assoc-rows (r (matrix->rows m1))))
                       :in-theory (e/d (m-+) ()))))

(defthmd m-+-comm-cols
  (implies (summable-p m1 m2)
           (equal (m-+--cols m1 m2 r c)
                  (m-+--cols m2 m1 r c)))
  :hints (("Goal" :in-theory (e/d (m-+--cols) ()))))

(defthmd m-+-comm-rows
  (implies (summable-p m1 m2)
           (equal (m-+--rows m1 m2 r)
                  (m-+--rows m2 m1 r)))
  :hints (("Goal" :in-theory (e/d (m-+--rows m-+-comm-cols) ()))))

(defthmd m-+-comm
  (equal (m-+ m1 m2)
         (m-+ m2 m1))
  :hints (("Goal" :expand ((m-+ m1 m2) (m-+ m2 m1))
                  :in-theory (e/d (m-+-comm-rows) ()))))
