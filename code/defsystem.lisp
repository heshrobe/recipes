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
   ("predicate-definitions" (:module-class separate-destination-joshua-module))
   ("read-gary-dump" (:module-class separate-destination-joshua-module))
   ("read-gary-ontoloty" (:module-class separate-destination-joshua-module))
   ("output-dumper" (:module-class separate-destination-joshua-module))
   ))


#|

;;; note: there are several files in this directory
;;; that were used in a standalone version that took
;;; START texps and then executed (like the guide system for ASIST does)
;;; In this project, we get Gary's IMPACT representation which was derived
;;; from the START parse.  I've removed those files from the defsystem
;;; but left then in the git repo.


Here's the mapping from files to their status

In the current system:

package-definition.lisp
predicate-definitions.lisp
read-gary-dump.lisp
read-json-ontology.lisp
output-dumper.lisp

Examples of processing Gary's output:

gary-ontology.lisp
expansion-example.lisp

Used in the standalone version:

parse-recipe.lisp
object-definitions.lisp

Supplanted by the planning-core system:
stateful-predicates.lisp



|#
