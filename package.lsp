(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

(defpkg "MAT"
  (set-difference-eq-exec
   (union-eq
    *acl2-exports*
    *common-lisp-symbols-from-main-lisp-package*
    *std-pkg-symbols*
    '(acl2::lnfix))
   '(set::delete set::union)))
