;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

 
(define-object-type recipe-object 
    :slots ()
    )

;;; This magic makes it be the case that when forward rules trigger off of object-type
;;; they use recipe's object-type-of predication as opposed to ltms:object-type-of
(defmethod ji::type-of-predicate-for-object-type ((thing recipe-object)) 'object-type-of)
(defmethod ji::part-of-predicate-for-object-type ((thing recipe-object)) 'named-component)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro define-recipe-object-type (name &rest plist)
    (let* ((super-types (getf plist :super-types))
	   (slots (getf plist :slots)))
      (loop for slot in slots
	  unless (getf (rest slot) :truth-maintenance)
	  do (setf (getf (rest slot) :truth-maintenance) 'value-of))
      (setf (getf plist :included-object-types) `(,@super-types recipe-object)
	    (getf plist :tms) t)
      (remf plist :super-types)
      )
    `(define-object-type ,name ,@plist)))

(defmethod intern-object (name type &rest arglist)
  (let ((existing-object (follow-path (list name) t nil)))
    (unless existing-object
      (setq existing-object
        (apply #'make-object type 
               :name name
               arglist)))
    existing-object))
