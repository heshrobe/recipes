;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Define-goal macro & achieve goal predicate
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *all-goals* nil)

(defmacro define-goal (name variables)
  `(eval-when (:load-toplevel :execute :compile-toplevel)
     (pushnew ',name *all-goals*)
     (define-predicate ,name ,variables (ltms:ltms-predicate-model))))

(define-predicate achieve-goal (goal-to-achieve input-state output-state plan) (ltms:ltms-predicate-model))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Utilities for the define-action macro
;;; Processes all the various fields
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun process-post-conditions (assertions output-state &optional support)
  (when assertions
    (if support
        (loop for assertion in assertions
	      collect `(tell [in-state ,assertion ,output-state]
                             ,@(when support
                                 `(:justification ,support))))
    `((prog1 t
	,@(loop for assertion in assertions collect `(tell [in-state ,assertion ,output-state])))))))

(defun process-assertions (assertions input-state)
  (labels ((do-one (assertion)
	     (cond
	      ;; special case for debugging
	      ((and (listp assertion) (not (predication-maker-p assertion)))
	       (if (eql (first assertion) 'break)
		   `(prog1 t ,assertion)
		 assertion))
	      ((eql (predication-maker-predicate assertion) 'or)
	       (with-predication-maker-destructured (&rest assertions) assertion
		 (loop for assertion in assertions
		     collect (do-one assertion) into processed-assertions
		     finally (return `(predication-maker '(or ,@processed-assertions))))))
	      ((and (listp assertion) (not (predication-maker-p assertion))) assertion)
	      ((compile-without-state assertion) assertion)
	      (t `(predication-maker '(in-state ,assertion ,input-state))))))
    (loop for thing in assertions collect (do-one thing))))


(defun process-guards (assertions input-state) (process-assertions assertions input-state))

(defun is-pretty-binding (assertion)
  (when (and (predication-maker-p assertion)
	     (eql (predication-maker-predicate assertion) 'value-of)
	     (with-predication-maker-destructured (path value) assertion
	       (if (and (not (logic-variable-maker-p path))
			(listp path))
		   nil
		 (and (logic-variable-maker-p value)
		      (find #\. (string (if (logic-variable-maker-p path)
					    (logic-variable-maker-name path)
					  path))
			    :test #'char-equal)))))
    t))

(defun de-prettify-binding (assertion)
  (with-predication-maker-destructured  (path logic-variable) assertion
    (flet ((process-path (list-of-strings)
	     (loop for thing in list-of-strings
		   if (char-equal (aref thing 0) #\?)
		   collect (ji::make-logic-variable-maker (intern thing))
		   else collect (intern thing))))
      (if (logic-variable-maker-p path)
	  (let* ((name (logic-variable-maker-name path))
		 (exploded-path (explode-string name #\.))
		 (real-path (cons (ji::make-logic-variable-maker (intern (first exploded-path)))
				  (process-path (rest exploded-path)))))
	  `(predication-maker '(value-of ,real-path ,logic-variable)))
      (let ((expanded-path (process-path (explode-string path #\.))))

	`(predication-maker '(value-of ,expanded-path ,logic-variable)))))))

(defun process-bindings (assertions input-state)
  (let ((expanded-bindings (loop for assertion in assertions
			       collect (if (is-pretty-binding assertion)
					   (de-prettify-binding assertion)
					 assertion))))
    (process-assertions expanded-bindings input-state)))

(defun process-prerequisites (assertions input-state) (process-assertions assertions input-state))

(defun compile-without-state (form)
  (if (predication-maker-p form)
    (let ((predicate (predication-maker-predicate form)))
      (cond
       ((eql predicate 'not)
	  (with-predication-maker-destructured (internal-pred) form
	    (let ((internal-predicate (predication-maker-predicate internal-pred)))
	      (subtypep internal-predicate 'non-stateful-predicate-model))))
       (t
	(or (subtypep predicate 'non-stateful-predicate-model)
	    (subtypep predicate 'ji::named-part-of-mixin)))))
    nil))

(defun process-typing (forms)
  (loop for form in forms
      if (and (listp form) (= (length form) 2))
      collect `(predication-maker '(object-type-of ,@form))
      else collect form))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Define-action macro and take-action predicate & link-action function
;;;
;;; Similar to but simpler than def-attack-method
;;; and it uses some of the sub-routines from def-attack-method
;;;
;;; Actions are defined over a set of logic-variables
;;;  Have pre-conditions that are tested in the input-state
;;;  and post-conditions that are asserted in the output-state
;;;
;;; If the output state is not passed in a new successor of the input state
;;; is created and unified with the output-state logic-variable
;;;
;;; Given that it's a mix of asks and tells should it be a backward rule or just a procedure that returns
;;; the output state?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-predicate take-action (action-name action input-state output-state) (ltms:ltms-predicate-model))
(define-predicate action-taken (action input-state output-state) (ltms:ltms-predicate-model))
(define-predicate check-prerequisites (action-name action input-state) (ltms:ltms-predicate-model))
(define-predicate prerequisite-satisfied (action-description prereq input-state) (ltms:ltms-predicate-model))
(define-predicate prerequisite-missing (action-description prereq input-state) (ltms:ltms-predicate-model))
;; Action-name and inputs are in fact outputs, i.e. they are bound by invoking a rule
(define-predicate action-and-inputs-to-achieve-condition (predication output-state action-name inputs) (ltms:ltms-predicate-model))

(defun link-action (action prior-state next-state)
  ;; mainly for debugging if you pass in a list of
  ;; the action-name and the arguments, then we'll
  ;; create the action argument
  (when (listp action)
    (destructuring-bind (name . arguments) action
      (setq action (make-instance 'action
                     :role-name name
                     :name name
                     :action-name name
                     :arguments arguments
                     :prior-state prior-state
                     :next-state next-state))))
  (setf (next-action prior-state) action
        (prior-action next-state) action
        (prior-state action) prior-state
        (next-state action) next-state
        )
  (link-state prior-state next-state)
  action)

(defun process-new-outputs (variable-list action-variable)
  (loop for (lv form name) in variable-list
      when (symbolp form)
      collect `(unify ,lv (make-object ',form :name (make-name ',form)))
      else collect `(unify ,lv ,form)
      collect `(let ((the-output (joshua-logic-variable-value ,lv))
                     (the-action (joshua-logic-variable-value ,action-variable)))
                 (push (list ',name the-output) (outputs the-action)))))

(defparameter *all-actions* nil)

(defun lv-thing-name (thing)
  (cond
   ((logic-variable-maker-p thing) (logic-variable-maker-name thing))
   ((unbound-logic-variable-p thing) (logic-variable-name thing))
   (t thing)))

(defmacro define-action (name inputs &key bindings prerequisites post-conditions (define-predicate t) super-types outputs typing abstract)
  ;; capture what was typed in
  (let ((source-inputs inputs)
        (source-outputs outputs)
        (source-prerequisites prerequisites)
        (source-post-conditions post-conditions)
        (source-typing typing))
    ;; now inherit the source forms from all super types
    (labels ((do-one-supertype (type-name)
               (let ((the-type (gethash type-name *action-type-ht*)))
                 (setq inputs (remove-duplicates (append (source-inputs the-type) inputs) :test #'equal :from-end t)
                       outputs (remove-duplicates (append (source-outputs the-type) outputs) :test #'equal :from-end t)
                       prerequisites (remove-duplicates (append (source-prerequisites the-type) prerequisites) :test #'equal)
                       post-conditions (remove-duplicates (append (source-post-conditions the-type) post-conditions) :test #'equal)
                       typing (remove-duplicates (append (source-typing the-type) typing) :test #'equal)
                       outputs (remove-duplicates (append (source-outputs the-type) outputs) :test #'equal))
                 (loop for type in (super-types the-type) do (do-one-supertype type)))))
      (loop for type in super-types do (do-one-supertype type)))
    (let (;; (source (generate-source name source-inputs source-prerequisites source-post-conditions source-outputs source-typing))
          (hidden-bindings-alist (find-bindings prerequisites post-conditions typing))
          (bindings-for-prereqs bindings)
          (bindings-for-post-conditions bindings)
          (bindings-for-typing bindings)
          (raw-prerequisites prerequisites)
          (raw-post-conditions post-conditions)
          (raw-inputs (mapcar #'lv-thing-name inputs))
          (raw-outputs (loop for (name) in outputs collect (lv-thing-name name)))
          (raw-output-typing (loop for (name type) in outputs collect (list name type)))
          (raw-typing typing))
    (multiple-value-setq (prerequisites post-conditions typing) (substitute-hidden-variables prerequisites post-conditions typing hidden-bindings-alist))
    (loop for (dotted-form lv) in (second (assoc 'prerequisites hidden-bindings-alist))
        do (push (ji:make-predication-maker `(value-of ,dotted-form ,lv)) bindings-for-prereqs))
    (loop for (dotted-form lv) in (second (assoc 'typing hidden-bindings-alist))
        do (push (ji:make-predication-maker `(value-of ,dotted-form ,lv)) bindings-for-typing))
    (loop for (dotted-form lv) in (second (assoc 'post-conditions hidden-bindings-alist))
          do (push (ji:make-predication-maker `(value-of ,dotted-form ,lv)) bindings-for-post-conditions))
    (flet ((make-logic-variables (names)
             (loop for var in names
                 if (logic-variable-maker-p var)
                 collect var
                 else collect `(logic-variable-maker ,(intern (string-upcase (format nil "?~a" var))))))
           (make-symbols-from-lvs (lvs)
             (loop for lv in lvs
                 for name = (logic-variable-maker-name lv)
                 for pname-string = (subseq (string name) 1) ;; strip off the ?
                 collect (intern pname-string))))
      (let* ((logic-variables (make-logic-variables inputs))
             (names (make-symbols-from-lvs logic-variables))
             (rule-name (intern (string-upcase (format nil "do-~a" name))))
             (jusification-mnemonic (intern (string-upcase (format nil "prerequisites-satisfied-~a" name))))
             (state-logic-variables (make-logic-variables '(input-state output-state)))
             (action-variable (first (make-logic-variables '(action)))))
        (destructuring-bind (input-state-variable output-state-variable) state-logic-variables
          `(eval-when (:compile-toplevel :load-toplevel :execute)
             (pushnew ',name *all-actions*)
             ,(define-action-type-creator name
                  :prerequisites raw-prerequisites
                  :post-conditions raw-post-conditions
                  :inputs raw-inputs
                  :outputs raw-outputs
                  :output-typing raw-output-typing
                  :super-types super-types
                  :typing raw-typing
                  :source-inputs source-inputs
                  :source-outputs source-outputs
                  :source-typing source-typing
                  :source-prerequisites source-prerequisites
                  :source-post-conditions source-post-conditions
                  :abstract abstract)
             (let ((new-action-type (create-action-object ',name)))
               (thread-action-type new-action-type))
             ;; ,source
             ,@(when define-predicate `((define-predicate ,name ,names (,@super-types ltms:ltms-predicate-model))))
             ,(generate-prereq-checker name inputs
                                       (append (process-bindings bindings-for-prereqs input-state-variable)
                                               (process-bindings bindings-for-typing input-state-variable))
                                       prerequisites
                                       input-state-variable
                                       typing)
             ,@(unless abstract (generate-prereq-achievers name logic-variables post-conditions (process-typing typing)))
             (defrule ,rule-name (:backward)
               then [take-action ,name ?action ,@state-logic-variables]
               if [and (let ((arguments (arguments ?action)))
                         ;; unpack the arguments from the action object
                         ,@(loop for lv in logic-variables
                               collect `(unify ,lv (pop arguments)))
                         t)
                       ,@(process-bindings bindings-for-post-conditions input-state-variable)
                       ,@(process-typing typing)
                       ,@(process-prerequisites prerequisites input-state-variable)
                       ;; so at this point we've checked that the prerequisites are satisfied
                       (prog1 t
                         (when (unbound-logic-variable-p ,output-state-variable)
                           (unify ,output-state-variable
                                  (intern-state (intern (string-upcase (gensym "state-"))) ,input-state-variable)))
                         (let* ((action-taken-pred (tell [action-taken ?action ,input-state-variable ,output-state-variable]
                                                         :justification :none))
                                (justification (build-justification-from-backward-support ji::*backward-support*)))
                           (destructuring-bind (nothing true-stuff false-stuff unknown-stuff) justification
                             (declare (ignore nothing))
                             (justify action-taken-pred +true+ ',jusification-mnemonic true-stuff false-stuff unknown-stuff))
                           (unify ,action-variable (link-action ?action ,input-state-variable ,output-state-variable))
                         ,@(process-new-outputs outputs action-variable)
                           ,@(let* ((mnemonic (intern (string-upcase (format nil "action-taken-~A" name))))
                                    (justification-2 `(list ',mnemonic (list action-taken-pred))))
                               (process-post-conditions post-conditions output-state-variable justification-2))
                           ))
                       ]))))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; More utilities for define-action
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Generate a rule that can tell you what action is relevant for achieving a goal
;;; Says that this rule is relevant for all it's post-conditions
;;; To do: annotate the post-conditions for which are the primary
;;; and which are the side-effects

(defun generate-prereq-achievers (name inputs post-conditions typing)
  (loop for post-condition in post-conditions
      for rule-number from 1
      for rule-name = (smash "-"  name 'achiever (format nil "~d" rule-number))
      collect `(defrule ,rule-name (:backward)
                 then [action-and-inputs-to-achieve-condition ,post-condition ?output-state ,name ,inputs]
                 if [and ,@typing
                         ;; makes sure that the inputs are referenced in the body
                         ;; because otherwise they'll get optimzed out by the backward
                         ;; rule expanded in joshua:code;Objectmo.lisp
                         ,@(mapcar #'(lambda (thing) `(prog1 t ,thing)) inputs) t]
                 )))

;;; Generates the code to create an object that describes this action
;;; More or less duplicates what's in the generate rules but in an examinable form
(defun define-action-type-creator (name &key inputs outputs prerequisites post-conditions super-types typing output-typing
                                             source-inputs source-outputs source-prerequisites source-post-conditions source-typing
                                             abstract)
  (let* ((input-lv-names (mapcar #'lv-thing-name inputs))
         (output-lv-names (mapcar #'lv-thing-name outputs))
         (all-lv-names  (append input-lv-names output-lv-names))
         (typing (loop for (lv-maker type) in typing collect `(list ,(lv-thing-name lv-maker) ',type)))
         (output-typing (loop for (lv-maker type) in output-typing collect `(list ,(lv-thing-name lv-maker) ',type)))
         )
    `(defmethod create-action-object ((name (eql ',name)))
       (with-unbound-logic-variables (,@all-lv-names)
         (macrolet ((ji::known-lvs () ',all-lv-names))
           (make-instance 'action-type
             :name ',name
             :abstract ,abstract
             :prerequisites (list ,@prerequisites)
             :post-conditions (list ,@post-conditions)
             :inputs (list ,@input-lv-names)
             :outputs (list ,@output-lv-names)
             :super-types ',super-types
             :typing (list ,@typing)
             :output-typing (list ,@output-typing)
             :source-inputs ',source-inputs
             :source-outputs ',source-outputs
             :source-prerequisites ',source-prerequisites
             :source-post-conditions ',source-post-conditions
             :source-typing ',source-typing
             ))))))

;;; This one is for the dumper
;;; It outputs a form that describes the action
;;; This is probably redundant with the Object created above
;;; which could be interpreted to do the same
(defun generate-source (name variables prerequisites post-conditions outputs typing)
  `(defmethod describe-action ((name (eql ',name)))
     `(define-action ,',name :arguments ,',variables :outputs ,',outputs :prerequisites ,',prerequisites :post-conditions ,',post-conditions :typing ,',typing)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Dealing with dotted notation
;;; Expand into a binding of a new variable
;;; and replace all references
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-bindings (prerequisites post-conditions typing)
  (let ((refs nil))
    (labels ((do-one (form key)
               (cond
                ((and (predication-maker-p form) (eql (predication-maker-predicate form) 'value-of))
                 (with-predication-maker-destructured (slot value) form
                   (declare (ignore slot))
                   (do-one value key)))
                ((predication-maker-p form)
                 (do-one (predication-maker-statement form) key))
                ((logic-variable-maker-p form)
                 (do-one (logic-variable-maker-name form) key))
                ((listp form)
                 (loop for token in form do (do-one token key)))
                ((and (symbolp form) (find #\. (string form) :test #'char-equal))
                 (let ((entry (assoc key refs)))
                   (unless entry
                     (setq entry (list key nil))
                     (push entry refs))
                   (unless (member form (second entry) :key #'first :test #'equal)
                     (push (list form (ji:make-logic-variable-maker (make-name '?lv))) (second entry))))))))
      (Loop for prereq in prerequisites do (do-one prereq 'prerequisites))
      (loop for postcon in post-conditions do (do-one postcon 'post-conditions))
      (loop for type in typing do (do-one type 'typing))
      )
    refs))

(defun substitute-hidden-variables (prerequisites post-conditions typing reference-alist)
  (labels ((do-one (form key)
             (cond
              ((and (predication-maker-p form) (eql (predication-maker-predicate form) 'value-of))
               (with-predication-maker-destructured (slot value) form
                 (ji:make-predication-maker
                  (list (predication-maker-predicate form)
                        (explode slot #\.)
                        (do-one value key)))))
              ((predication-maker-p form)
               (ji:make-predication-maker
                (loop for token in (predication-maker-statement form)
                    collect (do-one token key))))
              ((and (logic-variable-maker-p form) (find #\. (string (logic-variable-maker-name form)) :test #'char-equal))
               (let* ((alist (second (assoc key reference-alist)))
                      (entry (assoc (logic-variable-maker-name form) alist)))
                 (second entry)))
              ((logic-variable-maker-p form) form)
              ((listp form)
               (loop for token in form collect (do-one token key)))
              ((and (symbolp form) (find #\. (string form) :test #'char-equal))
               (let* ((alist (second (assoc key reference-alist)))
                      (entry (assoc form alist)))
                 (second entry)))
              (t form))))
    (values
     (loop for prereq in prerequisites collect (do-one prereq 'prerequisites))
     (loop for postcon in post-conditions collect (do-one postcon 'post-conditions))
     (loop for type in typing collect (do-one type 'typing))))
  )



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Prerequsite Checcking
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun generate-prereq-checker (action-name logic-variables bindings prerequisites input-state-logic-variable typing)
  `(defrule ,(smash "-" action-name 'check-prerequisites) (:backward)
     then [check-prerequisites ,action-name ?action ,input-state-logic-variable]
     if [and (let ((arguments (arguments ?action)))
               ,@(loop for lv in logic-variables
                     collect `(unify ,lv (pop arguments)))
               t)
               ,@bindings
             ,@(process-typing typing)
             ,@(loop for raw-prereq in prerequisites
                   collect `(check-one-prerequisite ',action-name ?action ,raw-prereq ,input-state-logic-variable))]))

;;; The workhorse for the rule generated above
;;; Notice the juggling that goes on if the prerequisite is negated
;;; You have to ask [not [in-state xxx] state] as opposed to [in-state [not xxx] state]
;;; Note: This assumes that all prerequisites are stateful
(defun check-one-prerequisite (action-name action prerequisite input-state)
  (declare (ignore action-name))
  (let* ((found-it nil)
         (prerequisite-is-negated (typep prerequisite 'ji::not-model))
         (prerequisite-is-non-stateful (typep prerequisite 'non-stateful-predicate-model))
         (thing-to-be-told (cond
                            (prerequisite-is-non-stateful prerequisite)
                            (prerequisite-is-negated `[not [in-state ,(second (predication-statement prerequisite)) ,input-state]])
                            (t `[in-state ,prerequisite ,input-state])))
        ;;; I could probably do this with forward rules, but the TMS hacking is more direct and less overhead
         (stateful-pred (tell thing-to-be-told :justification :none))
         (satisfied-pred (tell `[prerequisite-satisfied ,action ,prerequisite ,input-state]
                               :justification `(there-means-satisfied (,stateful-pred))))
         (missing-pred (tell `[prerequisite-missing ,action ,prerequisite ,input-state]
                             :justification `(not-there-means-missing () (,stateful-pred)))))
    ;; because of he way inheritance works across states, we need to make this check first
    ;; I.e. just the TMS'ing hack won't work without this
    (ask* (if prerequisite-is-negated `[not ,stateful-pred] stateful-pred)
          (setq found-it t))
    (unless found-it
      ;; This will automatically retract the assumption if it leads to a contradiction
      ;; We need to wrap any step that might cause a contradition, like when we try
      ;; to achieve a missing prerequisite
      (with-automatic-unjustification
          (assume `[not ,stateful-pred])))
    (values t satisfied-pred missing-pred)))

;;; A convenience function for scripting.  Just invokes the method
;;; which in turn invokes the function above.
(defun check-prerequisites (action state)
  (when (symbolp state)
    (setq state (intern-state state)))
  (let ((action-name (name action)))
    (ask* `[check-prerequisites ,action-name ,action ,state]
          t))
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Achieving missing prerequisites
;;;  Simple backward chaining gap filling planner
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; things to do here:
;;; Given a missing prereq and a relevant action what are the arguments to that action
;;;  maybe that could have been generated by the achieve-condition rule?
;;; Check that you succeeded, that's just a truth-value check?
;;; Run the prereq-checker for the action and see if there are missing prereqs
;;; in the new state.  If so recurse until either you've got the all or you fail
;;; in which case unthread all the intermediate states.
;;; Note that this creates a linear sequence of states
;;; dependency analysis can form this into a non-linear plan
;;; based on what post-conditions of which actions were relevant to achieve
;;; the pre-conditions of sucessors
;;; But then you need a 2nd step doing conflict analysis on the candidate non-linear
;;; plan (as in the heuristic forward search planners).
;;; This implies that the state model should allow states to have multiple predecessors
;;; which will complexify the calculation that tells you whether a predication is true in
;;; a state by searching the predecessors.

(defun find-all-missing-prerequisites (final-state)
  (when (symbolp final-state) (setq final-state (intern-state final-state)))
  (loop for state in (state-trace final-state)
      do (format t "~2%~a ~{~a~^, ~}" (state-name state) (nicknames state))
         (loop for prereq in (find-missing-prerequisites-in-state state)
             do (print prereq))))

(defun find-missing-prerequisites-in-state (state)
  (when (symbolp state) (setq state (intern-state state)))
  (let ((answer nil))
    (ask `[prerequisite-missing ?action-description ?prereq ,state]
         #'(lambda (just)
             (Push (ask-database-predication just) answer)))
    answer))

;;; Fix: If there are multiple prereqs then it's possible that the
;;; first action already achieved a prereq for an action needed to achieve
;;; a second prereq.  This currently misses that because the second prereq isn't
;;; satisfied and the relevant action's prereq is satisfied in the before state
;;; for the intended action, but it's trying to take the action in the state before that.
;;; So I think that when you achieve a missing prereq you need to create a new before state.
;;; Returns the state in which the prerequisite holds.  If the prereq is already true
;;; that's the state passed in.  Otherwise it's the output state of the action taken
;;; to achieve the prereq.

;;; Picture of state structure
;;;
;;;    previous-action -> output-state -> input-state -> this-action -> output-state

(defun achieve-missing-prerequisite (prerequisite-missing-pred input-state)
  (when (symbolp input-state) (setq input-state (intern-state input-state)))
  ;; Check whether it hasn't been achieved yet
  ;; IF so work to do, otherwise just return the state
  (if (eql (predication-truth-value prerequisite-missing-pred) +true+)
      (with-statement-destructured (action-description prerequisite input-state) prerequisite-missing-pred
        (declare (ignore action-description))

        (flet ((check-it ()
                 (ask `[in-state ,prerequisite ,input-state]
                      #'(lambda (just)
                          (let ((real-pred (ask-database-predication just)))
                            (tell `[in-state ,prerequisite ,input-state]
                                  :justification `(state-inheritance (,real-pred)))
                            (return-from achieve-missing-prerequisite))))))
          ;; The reason this is here is that the prereq might have been achieved
          ;; in a prior state and the inheritance across states isn't proactive
          ;; so the missing-prequisite statement is still in even thought the prereq
          ;; is achieved.  If it's achieved, this will get us out.
          (check-it)
          (when (eql (predication-truth-value prerequisite-missing-pred) +true+)
            (let ((predecessor-state (predecessor input-state)))
              ;; So if we need to take an action it will fall between
              ;; the output-state of the last action and the input-state
              ;; so the input-state of this new action needs to be linked to the previous
              ;; output-state and the output-state of this new action needs to be linked to the input state
              (block try-it
                (with-automatic-unjustification
                  ;; This will just return the name of a relevant action and the relevant inputs
                  ;; that can achieve the prereq
                  (ask* `[action-and-inputs-to-achieve-condition ,prerequisite ,input-state ?relevant-action ?inputs]
                        ;; now we know a pair of action and args that might achieve the prereq
                        ;; we need to make an input and output state for this action
                        ;; do-action will link the new input state to the predecessor
                        (let ((new-input-state (intern-state (smash "-" 'before ?relevant-action) nil))
                              (new-output-state (intern-state (smash "-" 'after ?relevant-action) nil)))
                          ;; This will recursively try to achieve the prequisites of that action
                          ;; if they aren't satisfied
                          (apply #'do-action ?relevant-action predecessor-state new-input-state new-output-state ?inputs)
                          ;; Linking the output state for this action to the input-state will
                          ;; cause predication inheritance across the states
                          (link-state new-output-state input-state)
                          ;; If we've achieved it we get out
                          (check-it))
                        (break "Failed action ~a for ~a in state ~a" ?relevant-action prerequisite input-state))))))))
      ;; (unthread-state input-state new-state state)
      ;;  The prereq was no longer missing so just return the state you came in with
      input-state))

;;; Note think about prereqs that are negated



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Do-action: Applying an action
;;;  This is called from either NLP or a script based on the recipe
;;;  Uses the prerequisite checking stuff above to see if the prereqa are satisfied
;;;
;;; Tries to achieve all missing prerequisites
;;; If successful, it then calls the take-action rule created by the define-action form
;;; Binds variables and then asserts the post conditions

;;; This is essentially a convenience function for scripting.
;;; Just invokes the method defined by the define-action form
;;;
;;; The model for states and actions is as follows:
;;;  Each action has an input state and an output state
;;;  The output state of one action is linked to the input state of the next
;;;  action, by a null action.  The prerequisite conditions are asserted in the input state.
;;;  This allows easy insertion of new actions to fulfill unsatisfied prerequisites.
;;;
;;;  We have 3 assertions associate with each prereq:
;;;   1) Prerequisite-missing (action prereq input-state)
;;;   2) Prerequisite-satisfied (action prereq input-state)
;;;   3) The actual prereq in the input state
;;;   Justifications link these:
;;;    The missing statement 1) depends on the negation of 3
;;;    The satisfied statement 3) depends on 3
;;;    The pred itself is assumed to be false.
;;;    The TMS takes care of the rest
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This needs to be fixed up so that it chains the achievement of prerequisites
;;; and iterates until all prerequisites are achieved
;;; I.e. recursive sub-goaling until the operator is applicable.
;;; Our assumption for interpreting recipes is that there are a set of operators
;;; that can achieve the prerequisites.
;;; Don't actually take the action unless the prereqs are satisfied
;;; Also need to undo the state action chain for each failed attempt to
;;; achieve a prereq.
;;;
;;; Is called with the name of the output state of the previous action
;;; and the names for new input and output states of this action
;;; as well as the arguments to the action
;;; It interns the input and ouptut states and links the input state
;;; to the output state of the previous action.

(defun do-action (action-name previous-output-state input-state output-state &rest arguments)
  (when (symbolp previous-output-state) (setq previous-output-state (intern-state previous-output-state nil)))
  (when (symbolp input-state) (setq input-state (intern-state input-state nil)))
  (when (symbolp output-state) (setq output-state (intern-state output-state input-state nil)))
  ;; Link input state to previous output-state with null action
  ;; this will cause predication inheritance from previous states
  (link-state previous-output-state input-state)
  (let ((action (make-instance 'action :name action-name :role-name action-name :arguments arguments)))
    (check-prerequisites action input-state)
    ;; Note that achieve-missing-prerequisite checks that the prereq is still missing
    ;; it might have been achieved serendipitously by achieving another prereq
    ;; This will thread in all needed actions and their states between the previous action's
    ;; output state and the input state with the missing prereqs
    ;; If there are more than 1 missing prereqs their relevant actions are sequenced
    ;; in between the previous output state and the input state in the order that they
    ;; are listed by find-missing-prerequisites-in-state
    (loop for missing-prereq in (find-missing-prerequisites-in-state input-state)
        do (achieve-missing-prerequisite missing-prereq input-state))
    ;; We're assuming here that we were successful in achieving all the prerequisites
    ;; Otherwise the take-action rule will fail.
    ;; This has the effect of asserting the post-conditions in the output-state
    (ask* `[take-action ,action-name ,action ,input-state ,output-state]
          ))
  output-state)

#|

(defun take-action (action input-state output-state)
  (when (symbolp input-state) (setq input-state (intern-state input-state)))
  (cond ((null output-state) (setq output-state (intern-state (make-name 'output) input-state)))
        ((symbolp output-state) (setq output-state (intern-state output-state input-state))))
  (let ((action-name (name action)))
    (ask* `[take-action ,action-name ,action ,input-state ,output-state]
          ))
  (values (prior-action output-state) output-state))

|#



(defun named-output (action name)
  (second (assoc name (outputs action))))

(defun type-check-arg (values action-type-name)
  (let* ((action-type (get-action-definition action-type-name))
         (inputs (inputs action-type))
         (typing (typing action-type)))
    (with-unification
     (loop for value in values
         for input in inputs
         do(unify value input))
     (loop for (value type) in typing
         for actual-value = (ji::joshua-logic-variable-value value)
         do (when (not (typep actual-value type))
              (format t "  failing")
              (ji::unify-fail))
         finally (return t))
     )))

(define-recipe-predicate possible-referent (word object referent) ())

;;; The word might refer to a part of the object
(defrule possible-referent-through-part-of (:backward)
  :then [possible-referent ?word ?object ?referent]
  :if [part-of ?object ?referent])

(defrule possible-referent-through-super-part (:backward)
  :then [possible-referent ?word ?object ?referent]
  :if [part-of ?referent ?object])

(defrule possible-referent-is-identity (:backward)
  :then [possible-referent ?word ?object ?object]
  :if t)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Converting the list structured attack plan into a fully backpointered
;;; plan linking in the actions and states
;;; This is for composite methods in an HTN, not really using it here yet
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun structure-attack-plan (top-level)
  (labels ((make-goal (goal-element &optional parent)
	     (let ((goal-statement (getf goal-element :goal))
		   (sub-plan (getf goal-element :plan)))
	       ;; (format t "~%Working on goal ~a" goal-statement)
	       (destructuring-bind (goal-name . arguments) goal-statement
		 (let* ((goal-object (make-instance 'goal :goal-name goal-name :arguments arguments :parent parent))
			(plan-object (make-plan sub-plan goal-object)))
		   (setf (plan goal-object) plan-object)
		   goal-object))))
	   (make-plan (plan-element parent)
	     (let ((connective (first plan-element))
		   (steps (rest plan-element)))
	       ;; (format t "~%For goal ~a with connective ~a there are ~a steps" parent connective (length steps))
	       (let* ((plan-object (make-instance 'plan
				  :connective connective
				  :parent parent))
		      (the-steps (loop for step in steps
				     for type = (first step)
				     for step-object = (case type
							 (:goal (make-goal step plan-object))
							 (:action (make-action step plan-object)))
				     ;; do (format t "~%For type ~a step ~a" type step-object)
				     collect step-object)))
		 ;; (format t "~%Steps for plan ~a ~{~a~^, ~}" plan-object the-steps)
		 (setf (steps plan-object) the-steps)
		 plan-object)))
	   (make-action (step parent)
	     (destructuring-bind (head list-version actual-action) step
	       (declare (ignore head list-version))
	       (setf (parent actual-action) parent)
	       actual-action)))
    (make-goal top-level)))

(defun attach-logic-variable-to-predication-maker (predication-maker logic-variable-maker)
  (let ((new-statement (append (predication-maker-statement predication-maker)
			       (list logic-variable-maker))))
    `(predication-maker ',new-statement)))

(defun rebuild-plan-structure (plan-structure &optional (input-state `(logic-variable-maker .(intern (string-upcase "?input-state"))))
							(output-state `(logic-variable-maker ,(intern (string-upcase "?output-state")))))
  ;; as we traverse the plan-structure tree we accumulate the list structure
  ;; of the plan and push
  ;; each this returns 3 values.  I'm not sure why the third yet
  (labels ((do-next-level (structure connective input-state output-state)
	     ;; each level should either be a :sequential/:parallel
	     ;;  or a :goal/:plan pair
	     ;;  or maybe a :action item (to be dealth with later)
             (destructuring-bind (key . stuff) structure
               (case key
                 (:sequential
                  (loop for (thing . more-to-come) on stuff
		      for last = (not more-to-come)
		      for next-input-state = input-state then his-output-state
		      for next-output-state = (when last output-state)
		      for his-result = (do-next-level thing key next-input-state next-output-state)
                      for (his-stuff his-plan-structure his-output-state) = his-result
                      append his-stuff into stuff
		      when his-plan-structure  ;; a note provides no plan structure
                      collect his-plan-structure into plan-structure
                      finally (let* ((is-singleton? (null (rest plan-structure)))
				     (final-key (if is-singleton? :singleton key)))
				(return (list stuff `(list ,final-key ,@plan-structure) his-output-state)))))
		 (:parallel
                  (loop for thing in stuff
		      for (his-stuff his-plan-structure) = (do-next-level thing key input-state output-state)
		      append his-stuff into stuff
		      when his-plan-structure ;; a note provides no plan structure
		      collect his-plan-structure into plan-structure
		      finally (return (list stuff `(list ,key ,@plan-structure) nil))))
		 (:bind
		  (let* ((the-binding (first stuff))
			 (input-state (or (getf structure :input-state)
					  input-state
					  (ji:make-logic-variable-maker (intern (string-upcase "?input-state")))))
			 (rebuilt-statement`(predication-maker '(in-state ,the-binding ,input-state))))
		    (list (list rebuilt-statement)
			  nil
			  input-state)))
		 (:note
		  (let* ((the-note (first stuff))
			 (input-state (or (getf structure :input-state)
					  input-state
					  (ji:make-logic-variable-maker (intern (string-upcase "?input-state")))))
			 (intermediate-state (or (getf structure :output-state)
						 output-state
						 (ji:make-logic-variable-maker (intern (string-upcase (gentemp "?intermediate-state-"))))))
			 (statement the-note)
			 (rebuilt-statement `(prog1 t (let ((new-state (intern-state (intern (string-upcase (gentemp "intermediate-state-"))) ,input-state)))
							(setf (intermediate-state? new-state) t)
							(unify ,intermediate-state new-state)
							(tell (predication-maker '(in-state ,statement ,intermediate-state)))))))
		    (list (list rebuilt-statement)
			  nil
			  intermediate-state)))
		 (:break (list (list `(prog1 t (break ,@stuff)))
			       nil
			       input-state))
                 ((:goal :plan)
                  (let* ((goal (getf structure :goal))
                         (plan (getf structure :plan (ji::make-logic-variable-maker (gentemp (string-upcase "?plan-") ))))
			 (input-state (or (getf structure :input-state)
					  input-state
					  (ji:make-logic-variable-maker (intern (string-upcase "?input-state")))))
			 (output-state (or (getf structure :output-state)
					   output-state
					   (ji:make-logic-variable-maker (intern (string-upcase (gentemp "?intermediate-state-"))))))
                         (rebuilt-statement `(predication-maker '(achieve-goal ,goal ,input-state ,output-state ,plan))))
                    (list (list rebuilt-statement)
                          (if (null connective)
                              `(list :singleton
                                     (list :goal ,(fixup-syntax (predication-maker-statement goal))
                                           :plan ,plan))
                            `(list :goal ,(fixup-syntax (predication-maker-statement goal))
                                   :plan ,plan))
			  output-state)))
                 ((:action :repeated-action)
		  (let* ((statement (first stuff))
			 (input-state (or (getf structure :input-state)
					  input-state
					  (ji::make-logic-variable-maker (intern (string-upcase "?input-state")))))
			 (output-state (or (getf structure :output-state)
					   output-state
					   (ji:make-logic-variable-maker (intern (string-upcase (gentemp "?intermediate-state-"))))))
			 (action-variable (ji:make-logic-variable-maker (intern (string-upcase (gentemp "?action-")))))
			 (rebuilt-statement `(predication-maker '(take-action ,statement ,input-state ,output-state ,action-variable)))
			 )
		    ;; (break "Action ~a ~a ~a ~a" statement input-state output-state rebuilt-statement)
		    (list
		     ;; The action requires no further sub-goaling
		     (list rebuilt-statement)
		   ;;; rebuilt action statement
		     (if (null connective)
			 `(list :singleton
				(list ,key ,(fixup-syntax (predication-maker-statement (first stuff))) ,action-variable))
		       `(list ,key ,(fixup-syntax (predication-maker-statement (first stuff))) ,action-variable))
		     output-state))))))
           (fixup-syntax (predication-maker-statement)
             `(list
               ,@(loop for thing in predication-maker-statement
                     collect (typecase thing
                               (logic-variable-maker thing)
                               (symbol `',thing)
                               (list (fixup-syntax thing)))))))
    (when plan-structure
      (do-next-level plan-structure nil input-state output-state))))


(defparameter *all-attack-methods* nil)

(defmacro define-method (method-name &key to-achieve
					     (input-state `(logic-variable-maker ,(intern (string-upcase "?input-state"))))
					     (output-state `(logic-variable-maker ,(intern (string-upcase "?output-state"))))
					     guards
					     bindings
					     prerequisites
					     typing
					     plan
					     post-conditions
					     )
  (let* ((plan-variable `(logic-variable-maker ,(gensym "?PLAN")))
         (real-head `(predication-maker '(achieve-goal ,to-achieve ,input-state  ,output-state ,plan-variable)))
	 (rebuilt-plan-structure (rebuild-plan-structure plan input-state output-state)))
    (destructuring-bind (stuff plan-structure thing) (or rebuilt-plan-structure (list nil nil nil))
      (declare (ignore thing))
      `(eval-when (:load-toplevel :execute)
         (pushnew ',method-name *all-attack-methods*)
         (defrule ,method-name (:backward)
         then ,real-head
         if [and
	     ,@(process-bindings bindings input-state)
	     ,@(process-guards guards input-state)
	     ,@(process-typing typing)
	     ,@(process-prerequisites prerequisites input-state)
	     ,@stuff
	     ,@(process-post-conditions post-conditions output-state)
	     ,@(when (null rebuilt-plan-structure)
	       `((unify ,input-state ,output-state)))
	     (unify ,plan-variable ,plan-structure)
	     ])))))
