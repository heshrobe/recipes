;;; -*- Mode: Common-lisp; Package: cl-user -*-

(in-package :cl-user)

(defpackage recipes
  (:use planning-core start joshua common-lisp)
  ;; note that we don't import part-of and named-part-of
  (:shadowing-import-from planning-core value-of object-type-of)
  (:shadow part-of named-part-of component time)
  (:shadow room)
  (:import-from ltms assume))
