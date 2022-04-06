;;; -*- Syntax: Ansi-common-lisp; Package: cl-USER; Base: 10; Mode: LISP -*-

(in-package :cl-user)

(defvar *recipes-home-directory* :not-yet)
(defvar *recipes-wild-directory* :not-yet)

(eval-when (:execute :load-toplevel)
  (let* ((loading-file *load-truename*)
         (host (pathname-host loading-file))
         (device (pathname-device loading-file))
         (home-dir (pathname-directory loading-file))
         (wild-dir (append (butlast home-dir) (list :wild-inferiors))))
    (setq *recipes-home-directory* (make-pathname :directory (butlast home-dir)
                                                :host host
                                                :device device)
          *recipes-wild-directory* (make-pathname :directory wild-dir
                                                :host host
                                                :device device
                                                :type :wild
                                                :name :wild
                                                :version :unspecific))
    (setf (logical-pathname-translations "recipes")
      `(("home;*.*"	,*recipes-home-directory*)
        ("**;*.*"	,*recipes-wild-directory*)
        ))
    (with-open-file (F #P"recipes:home;my-logical-pathnames.lisp" :direction :output :if-exists :supersede :if-does-not-exist :create)
      (format f "~%;;; recipes")
      (format f "~2%~s" "recipes")
      (loop for (a b) in (logical-pathname-translations "recipes")
          do (format f "~%'(~s ~s)" (namestring a) (namestring b)))
      (terpri f)
      )
    (pushnew (namestring (truename #P"recipes:home;my-logical-pathnames.lisp"))
             (logical-pathname-translations-database-pathnames)
             :test #'string-equal))
  )

#+allegro
(defsystem recipes
    (:default-pathname "recipes:code;"
        :default-module-class separate-destination-module)
  (:serial
   ("package-definition")
   ("basic-definitions" (:module-class separate-destination-joshua-module))
   ("stateful-predicates" (:module-class separate-destination-joshua-module))
   ("define-action" (:module-class separate-destination-joshua-module))
   ("define-object" (:module-class separate-destination-joshua-module))
   ("predicate-definitions" (:module-class separate-destination-joshua-module))))


(Defsystem recipes
    (:default-pathname "recipes:code;"
        :default-module-class separate-destination-module)
  (:serial
   ("object-definitions" (:module-class separate-destination-joshua-module))
   ("actions" (:module-class separate-destination-joshua-module))
   ("output-dumper" (:module-class separate-destination-joshua-module))
   ("parse-recipe" (:module-class separate-destination-joshua-module))
   ))
