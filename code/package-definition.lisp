;;; -*- Mode: Common-lisp; Package: cl-user -*-

(in-package :cl-user)

(defpackage recipes
  (:shadow value-of object-type-of)
  ;; (:shadowing-import-from )
  (:import-from ltms "ASSUME")
  (:export
   intern-state initial *initial-state* clear-all-states
   define-action do-action in-state 
   recipe-object 
   define-recipe-object-type define-recipe-predicate
   value-of intern-object
   action-sequence display-action-sequence state-trace
   object-type-of value-of
   define-fwrd-stateful-rule then
   non-stateful-predicate-model stateful-predicate-mixin
   prior-action next-action
   prior-state next-state
   action state
   predications-newly-in-state
   state-name
   action-taken
   smash
   make-name
   end-of-state-chain
   arguments
   )      
  (:use start joshua common-lisp))
