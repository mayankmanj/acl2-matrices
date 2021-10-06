;;; Matrix equality theorems

(in-package "MAT")

(include-book "definitions")

(local (in-theory (e/d (m-= m-=--rows m-=--cols) ())))

(encapsulate ()
  (local (defthm m-=--cols-refl
           (m-=--cols x x r c)))
  (local (defthm m-=--rows-refl
           (m-=--rows x x r)))
  (local
   (defthm m-=--cols-sym
     (implies (m-=--cols x y r c)
              (m-=--cols y x r c))))
  (local
   (defthm m-=--rows-sym
     (implies (m-=--rows x y r)
              (m-=--rows y x r))))
  (local (defthm m-=--cols-trans
           (implies (and (m-=--cols x y r c)
                         (m-=--cols y z r c))
                    (m-=--cols x z r c))))
  (local (defthm m-=--rows-trans
           (implies (and (m-=--rows x y r)
                         (m-=--rows y z r))
                    (m-=--rows x z r))))

  (defequiv m-=))

(defthmd m-=--cols-m-get
  (implies (and (m-=--cols m2 m2-e r col)
                (<= c col) (natp col))
           (equal (m-get m2 r c)
                  (m-get m2-e r c)))
  :hints (("Goal" :in-theory (e/d (m-get) ()))))

(defthmd m-=--rows-m-get
  (implies (and (m-=--rows m2 m2-e row)
                (<= r row) (natp row))
           (equal (m-get m2 r c)
                  (m-get m2-e r c)))
  :hints (("Goal" :in-theory (e/d (m-=--cols-m-get) ()))))

(defcong m-= equal (m-get m1 r c) 1
  :hints (("Goal" :in-theory (e/d (m-=--rows-m-get) ()))))

(defcong m-= equal (matrix->rows m) 1
  :hints (("Goal" :in-theory (e/d (m-=) ()))))

(defcong m-= equal (matrix->cols m) 1
  :hints (("Goal" :in-theory (e/d (m-=) ()))))
