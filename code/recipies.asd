;;; -*- Syntax: Ansi-common-lisp; Package: cl-USER; Base: 10; Mode: LISP -*- 

(in-package :cl-user)

(defvar *recipes-home-directory* :not-yet)
(defvar *recipes-wild-directory* :not-yet)

;;; If we're using swank (i.e. slime) then associate
;;; the joshua readtable with the RECIPES package
;;; so the we read in Joshua syntax

#+swank
(pushnew (cons "RECIPES" ji::*joshua-readtable*)
	 swank:*readtable-alist*
	 :key #'first
	 :test #'string=)


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
        )))
  )

#+asdf
(asdf:defsystem recipies/core
  :name "recipes-core"
  :description "Recipe Follower Functionality"
  :maintainer "Howie Shrobe"
  :pathname "."
  :components
  ((:file "package-definition")
     (:joshua-file "basic-definitions" :depends-on ("package-definition"))
     (:joshua-file "stateful-predicates" :depends-on ("basic-definitions")) 
     (:joshua-file "define-action" :depends-on ("stateful-predicates"))
     (:joshua-file "predicate-definitions" :depends-on ("define-action"))
     (:joshua-file "define-object" :depends-on ("predicate-definitions"))
     ))


#+asdf
(asdf:defsystem recipies 
  :name "recipes"
  :description "Stuff specific to interpreting cooking recipes"
  :maintainer "Howie Shrobe"
  :pathname "."
  :depends-on (recipies/core)
  :components
  ((:joshua-file "object-definitions")
   (:joshua-file "actions" :depends-on (object-definitions))
   (:joshua-file "output-dumper" :depends-on ("actions"))
   (:joshua-file "parse-recipe" :depends-on ("output-dumper"))
   ))
