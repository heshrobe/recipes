;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

;;;(define-recipe-predicate named-component (superpart-object name subpart-object)
;;;   (ji::named-part-of-mixin))

;;; (define-recipe-predicate component (superpart-object subpart-object) (ji::part-of-mixin))

(define-recipe-predicate value-of (path variable) (ji::slot-value-mixin))

;;; This is only used in fward-stateful-rule patterns to indicate that the value-of isn't stateful.
(define-recipe-predicate value-of-ns (path variable) (non-stateful-predicate-model ji::slot-value-mixin))

(define-recipe-predicate object-type-of (thing type) (non-stateful-predicate-model type-of-mixin))

;;; For the recipe system we don't use the object-model from Joshua

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

(define-recipe-predicate part-of (component container) ())




(define-recipe-predicate contains (container contents) ())

(define-recipe-predicate above (thing container) ())

(define-recipe-predicate in (thing container) ())

(define-recipe-predicate has (actor object) ())

(define-recipe-predicate broken (thing) ())

(define-recipe-predicate ingredient-of (recipe thing) ())

(define-recipe-predicate utensil-of (recipe thing) ())

(define-recipe-predicate appliance-of (recipe thing) ())

(define-recipe-predicate cook-of (recipe cook) ())

(define-recipe-predicate constituent-of (thing mixture) ())

(define-recipe-predicate state-of (thing its-state) ())

(define-recipe-predicate is-folded (thing) ())

(define-recipe-predicate is-flexible (thing) ())

(define-recipe-predicate holding (actor object) ())
(define-recipe-predicate handempty (actor) ())

(define-recipe-predicate is-prepared (thing type) ())
