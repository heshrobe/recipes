;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

(defun reformat-stateful-predication (stateful-pred)
  (let* ((truth-value (predication-truth-value stateful-pred))
         (internal-pred (second (predication-statement stateful-pred)))
         (statement (predication-statement internal-pred)))
    (labels ((do-one (level)
               (typecase level
                 (ji::unbound-logic-variable (ji::joshua-logic-variable-name level))
                 (list 
                  (loop for thing in level
                      collect (do-one thing)))
                 (recipe-object (apply #'smash "." (path-name level)))
                 (predication
                  (do-one (Predication-statement level)))
                 (t level))))
      (let ((answer (do-one statement)))
        (if (eql truth-value +false+)
            (list 'not answer)
          answer)))))

(defun reformat-statement (statement)
  (labels ((do-one (level)
             (typecase level
               (ji::unbound-logic-variable (ji::joshua-logic-variable-name level))
               (list 
                (loop for thing in level
                    collect (do-one thing)))
               (recipe-object (apply #'smash "." (path-name level)))
               (predication
                (do-one (Predication-statement level)))
               (t level))))
    (do-one statement)))

(defun describe-action (action-name)
  (let ((action (gethash action-name *action-type-ht*)))
    (when action
      `(define-action ,action-name
           :arguments ,(mapcar #'ji::joshua-logic-variable-name (inputs action))
           :outputs ,(mapcar #'ji::joshua-logic-variable-name (outputs action))
           :prerequisites ,(mapcar #'reformat-statement (prerequisites action))
           :post-conditions ,(mapcar #'reformat-statement (post-conditions action))
           :typing ,(append (loop for (variable type) in (typing action) collect (list (ji::joshua-logic-variable-name variable) type))
                            (loop for (variable type) in (output-typing action) collect (list (ji::joshua-logic-variable-name variable) type)))))))

(defun dump-results (final-state &optional (stream *standard-output*))
  (setq final-state (intern-state final-state))
  (format stream "~%State Sequence")
  (loop for state in (state-trace final-state)
      for next-state = (first (successors state))
      for next-action = (next-action state)
      when next-action
      do (format stream "~%State ~a Next action ~a Next State ~a"
                 (state-name state) (role-name next-action) (state-name next-state))
      )
  (format stream "~%State Contents")
  (loop for state in (state-trace final-state)
      for preds = (predications-newly-in-state state)
      do (format stream "~%~2tState ~a" (state-name state))
         (loop for pred in preds
             do (format stream "~%~4t~a" (reformat-stateful-predication pred)))) 
  (format stream "~%Missing Prerequisites")
  (ask* `[prerequisite-missing ?action ?prereq ?state]
        (format stream "~%~2t~a for action ~a in state ~a"
                (reformat-statement (predication-statement ?prereq))
                (reformat-statement ?action)
                (state-name ?state)))
  (format stream "~%Action Definitions")
  (loop with already-done
      for action in (action-sequence final-state)
      for action-name = (name action)
      unless (member action-name already-done)
      do (push action-name already-done)
         (print (describe-action action-name) stream))
  )

