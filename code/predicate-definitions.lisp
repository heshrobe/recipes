;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; This system is based on Joshua and the planning-core extension.
;;;
;;; Use of Joshua's object model:
;;; We use the Joshua object model, with the predicates object-type-of and value-of
;;; Value-of is a predicate that is temporally qualified (i.e. [in-state [value-of ... ]])
;;; But object-type-of isn't.
;;; We don't use the joshus object-model part-of and named-part-of because the planning-core
;;; extension doesn't support making those temporally qualified.  So we just have a vanilla
;;; part of predicate.
;;; object-type-of isn't termporally quafilied which means that an object can't change it's type.
;;; instead we have a 1-place predicate exists that is temporally qualified.
;;; When a new object is created. the assert that it didn't exist in the initial state and that
;;; it exists in the object state of the action that created it.  (This will require a small modification
;;; to define-aciton in planning-core).
;;; If an object is transformed (e.g. eggs are sliced) we assert that the original object (the eggs) no longer exists
;;; and that the transformed object is newly created (the slices) and that it is derived from the original
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-planning-predicate named-part-of (superpart-object name subpart-object) ())

(define-planning-predicate part-of (superpart-object subpart-object) ())

(define-planning-predicate component (superpart-object subpart-object) ())

(define-planning-predicate product-of (source result) ())

;;; This is only used in fward-stateful-rule patterns to indicate that the value-of isn't stateful.
;;; (define-recipe-predicate value-of-ns (path variable) (non-stateful-predicate-model ji::slot-value-mixin))

;;; We do use object-type-of from Joshua and its inheritance mechanisms
;;; so this code isn't needed.  I'm just not quite ready to remove it from the
;;;

#|

(define-recipe-predicate instance-of (thing type) ())
(define-recipe-predicate subtype (type1 type2) (non-stateful-predicate-model))

(defun find-all-supers (type)
  (let ((all-supers nil))
    (labels ((do-one (super)
               (cond
                ((member super all-supers))
                (t (unless (eql super type)
                     (push super all-supers))
                   (ask `[subtype ,super ?next]
                        #'(lambda (just)
                            (declare (ignore just))
                            (do-one ?next))
                        :do-backward-rules nil)))))
      (do-one type))
    all-supers))

(defun find-all-subs (type)
  (let ((all-subs nil))
    (labels ((do-one (sub)
               (cond
                ((member sub all-subs))
                (t (unless (eql sub type)
                     (push sub all-subs))
                   (ask `[subtype ?next ,sub]
                        #'(lambda (just)
                            (declare (ignore just))
                            (do-one ?next))
                        :do-backward-rules nil)))))
      (do-one type))
    all-subs))

(defrule sub-type-inheritance-1 (:backward)
  :then [subtype ?a ?b]
  :if [and (not (unbound-logic-variable-p ?a))
           (loop for super in (find-all-supers ?a)
               do (unify super ?b)
                  (succeed))])


(defrule sub-type-inheritance-2 (:backward)
  :then [subtype ?a ?b]
  :if [and (not (unbound-logic-variable-p ?b))
           (loop for sub in (find-all-subs ?b)
               do (unify sub ?a)
                  (succeed))])

(defun find-all-types-of-object (the-object state &optional (immediate? t))
  (let ((all-supers nil))
    (ask `[in-state [instance-of ,the-object ?immediate-super] ,state]
         #'(lambda (just)
             (declare (ignore just))
             (cond
              ((member ?immediate-super all-supers))
              (t (when immediate? (push ?immediate-super all-supers))
                 (loop for super in (find-all-supers ?immediate-super)
                     do (pushnew super all-supers)))))
         :do-backward-rules nil)
    all-supers))

;;; Note this only handles the case where ?a is bound
;;; We could easily also do one that finds all instances of some supertype
(defrule inheritance-of-instance-of (:backward)
  :then [in-state [instance-of ?a ?b] ?state]
  :if [and (not (unbound-logic-variable-p ?a))
           (loop for super in (find-all-types-of-object ?a ?state nil)
               do (with-unification
                  (unify super ?b)
                  (succeed)))])

(defrule inheritance-of-instance-of-2 (:backward)
  :then [in-state [instance-of ?a ?b] ?state]
  :if [and (not (unbound-logic-variable-p ?b))
           (unbound-logic-variable-p ?a)
           (loop for sub in (find-all-subs ?b)
               do (ask `[in-state [instance-of ?a ,sub] ?state]
                       #'(lambda (just)
                           (declare (ignore just))
                           (succeed))
                       :do-backward-rules  nil))]
  )

|#




(define-planning-predicate contains (container contents) ())

(define-planning-predicate above (thing container) ())

(define-planning-predicate in (thing container) ())

(define-planning-predicate has (actor object) ())

(define-planning-predicate broken (thing) ())

(define-planning-predicate ingredient-of (recipe thing) ())

(define-planning-predicate utensil-of (recipe thing) ())

(define-planning-predicate appliance-of (recipe thing) ())

(define-planning-predicate cook-of (recipe cook) ())

(define-planning-predicate constituent-of (thing mixture) ())

(define-planning-predicate state-of (thing its-state) ())

(define-planning-predicate is-folded (thing) ())

(define-planning-predicate is-flexible (thing) ())

(define-planning-predicate holding (actor object) ())
(define-planning-predicate handempty (actor) ())

(define-planning-predicate is-prepared (thing type) ())
