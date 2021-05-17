;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

(define-recipe-predicate named-component (superpart-object name subpart-object) 
  (ji::named-part-of-mixin))

(define-recipe-predicate component (superpart-object subpart-object) (ji::part-of-mixin))

(define-recipe-predicate value-of (path variable) (ji::slot-value-mixin))

(define-recipe-predicate object-type-of (thing type) (non-stateful-predicate-model type-of-mixin))




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




