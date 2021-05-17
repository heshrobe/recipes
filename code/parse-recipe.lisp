;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

(defparameter *recipe-directory* #p"~/Research-Projects/langley/*.text")

(defun read-recipe (recipe-name)
  (let ((pathname (merge-pathnames (pathname recipe-name) *recipe-directory*)))
    (with-open-file (f pathname :direction :input)
      (loop for sentence = (read-line f nil 'eof)
          until (eql 'eof sentence)
          for parse = (parse-text sentence)
          do (print (string-for parse :viz))))))
