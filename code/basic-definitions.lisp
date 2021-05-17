;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

(defvar name-to-number-hash-table (make-hash-table))

(defun make-name (lead-in)
  (let ((existing-number (gethash lead-in name-to-number-hash-table)))
    (unless existing-number
      (setf (gethash lead-in name-to-number-hash-table) 0))
    (intern (string-upcase (format nil "~a-~d" lead-in (incf (gethash lead-in name-to-number-hash-table)))))))

(defun smash (delimiter &rest names)
  (let ((strings (loop for (name . rest) on names
                     for string = (string name)
                     collect string
                     when rest 
                     collect delimiter)))
    (intern (string-upcase (apply #'concatenate 'string strings)))))

(defun explode-string (string delim)
  ;; so it can handle a symbol
  (setq string (string string))
  (loop for last-pos = 0 then (1+ next-pos)
        for next-pos = (position delim string :start last-pos)
        collect (subseq string last-pos next-pos)
      until (null next-pos))
  )

(defmethod explode ((thing symbol) delimeter)
  (loop for string in (explode-string thing delimeter)
      collect (intern string)))

(defmethod explode ((thing list) delimeter)
  (if (logic-variable-maker-p thing)
      (destructuring-bind (first . rest) (explode (logic-variable-maker-name thing) delimeter)
        (list* (ji:make-logic-variable-maker first) rest))
    thing))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Classes for building a structured-backpointered plan object
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defclass has-parent-mixin ()
  ((parent :accessor parent :initform nil :initarg :parent)))

(defclass has-plan-mixin ()
  ((plan :accessor plan :initform nil :initarg nil)))

(defclass has-arguments-mixin ()
  ((arguments :accessor arguments :initarg :arguments)))

(defclass has-outputs-mixin ()
  ((outputs :accessor outputs :initarg :outputs :initform nil)))

(defclass has-inputs-mixin ()
  ((inputs :accessor inputs :initarg :inputs :initform nil)))

(defclass has-name-mixin ()
  ((name :accessor name :initarg :name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; data type for describing an action type
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *action-type-ht* (make-hash-table))

(defun get-action-definition (name) (gethash name *action-type-ht*))

(defclass action-type (has-name-mixin has-inputs-mixin has-outputs-mixin)
  ((prerequisites :accessor prerequisites :initarg :prerequisites :initform nil)
   (post-conditions :accessor post-conditions :initarg :post-conditions :initform nil)
   (super-types :accessor super-types :initarg :super-types :initform nil)
   (sub-types :accessor sub-types :initarg :sub-types :initform nil)
   (typing :accessor typing :initarg :typing :initform nil)
   (output-typing :accessor output-typing :initarg :output-typing :initform nil)
   (source-inputs :accessor source-inputs :initarg :source-inputs :initform nil)
   (source-outputs :accessor source-outputs :initarg :source-outputs :initform nil)
   (source-prerequisites :accessor source-prerequisites :initarg :source-prerequisites :initform nil)
   (source-post-conditions :accessor source-post-conditions :initarg :source-post-conditions :initform nil)
   (source-typing :accessor source-typing :initarg :source-typing :initform nil)
   (abstract :accessor abstract :initarg :abstract :initform nil)))

(defun thread-action-type (new-action-type)
  (let ((name (name new-action-type))
        (supers (super-types new-action-type)))
    (setf (gethash name *action-type-ht*) new-action-type)
    (loop for super-name in supers
        for super = (gethash super-name *action-type-ht*)
        do (pushnew name (sub-types super)))))


(defun walk-action-hierarchy (action-name continuation &key direction)
  (catch 'action-walker
    (labels ((do-one (action-name)
               (let ((action (get-action-definition action-name)))
                 (funcall continuation action)
                 (loop for action-names in (if (eql direction 'down) (sub-types action) (super-types action))
                     do (do-one action-name)))))
      (do-one action-name))))
    

(defclass state-transformer (has-name-mixin has-parent-mixin has-arguments-mixin has-outputs-mixin print-nicely-mixin)
  ((prior-state :accessor prior-state :initarg :prior-state) 
   (next-state :accessor next-state :initarg :next-state)
   (duration :accessor duration :Initarg :duration :initform nil)
   (exit-condition :accessor exit-condition :Initarg :exit-condition :initform nil))
  )

(defclass action (state-transformer)
  ((is-on-solution-path? :accessor is-on-solution-path? :initform nil)
   ))

(defclass physical-process (state-transformer)
  ()
  )

(defclass goal (has-parent-mixin has-plan-mixin has-arguments-mixin)
  ((goal-name :accessor goal-name :initform nil :initarg :goal-name))
  )

(defclass plan (has-parent-mixin)
  ((connective :accessor connective :Initform nil :initarg :connective)
   (steps :accessor steps :initform nil :initarg :steps)))

(define-object-type print-nicely-mixin)

(defvar *print-object-nicely* nil)

(defmethod print-object :around ((thing print-nicely-mixin) stream)
  (cond (*print-object-nicely*
         (let ((path (path-name thing)))
           (format stream "~{~a~^.~}" path)))
        (t (call-next-method))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Retellable Predicates
;;; 
;;; We'll have a list of predicates to retell and appropriate
;;; predicate-methods to make this work
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *predicates-to-retell* nil)

(define-predicate-model restorable-predicate () (ltms:ltms-predicate-model))

(define-predicate-method (tell restorable-predicate :after) (truth-value justification)
  ;; I'm assuming that all of these are premises
  (declare (ignore justification))
  (pushnew (list (predication-statement self) truth-value) *predicates-to-retell* :test #'equal))

(define-predicate-method (after-clear restorable-predicate :after) (&optional clear-database undefrules)
  (when (and clear-database (not undefrules))
    (loop for (statement truth-value) in *predicates-to-retell*
	if (eql truth-value +true+)
	do (let ((pred (make-predication statement)))
	     (ji:tell-internal pred +true+ :premise)
	     )
	else do
	   (let* ((inner-pred (make-predication statement))
		  (outer-pred `[not ,inner-pred]))
	     (tell outer-pred :justification :premise)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Macro for defining our predicates
;;;  Fill in ltms:ltms-predicate-model
;;;  collect predicate name in a global variable
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (:load-toplevel :compile-toplevel :execute)
  (defparameter *all-recipe-predicates* nil)
  
  (define-predicate-model recipe-predicate-model () (ltms:ltms-predicate-model))

  (defmacro define-recipe-predicate (name parameters models)
    (let ((all-models (if (member 'recipe-predicate-model models) 
                          models
                        (append models (list 'recipe-predicate-model)))))
      `(eval-when (:load-toplevel :compile-toplevel :execute)
         (pushnew ',name *all-recipe-predicates*)
         (define-predicate ,name ,parameters ,all-models)))))