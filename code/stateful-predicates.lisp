;;; -*- Mode: LISP; Syntax: Joshua; Package: recipes ; readtable: joshua -*-

(in-package :recipes)

;;; Notes: The interaction with negation makes this tricky.  
;;; Initially I thought you'd just like to have the predication
;;; without explicity mention of context and hide the context in a 
;;; slot.  But then you'd have to deal with truth-values differently
;;; since something can be true in one context and false in another
;;; and therefore the +true+, +false+ predication bits can't be used
;;; in the same way.
;;; Options: 1) Simple: just add the context as an explicity field part of the predication
;;; and use the inheritance stuff below.
;;; 2) Work through all the complexities of not having a unique truth value for a predication
;;; 3) Have a meta-predication [in-context [predication] foo]

;;; I'm going for 3.
;;; So your format is [in-state [foo 1 2 3] state-1] for
;;; positive assertions and [not [in-state [foo 1 2 3] state-2] for negative ones.
;;; Of course, the negated external form shows up as a +false+ truth-value on the whole
;;; assertion.  The embedded assertions are assumed to never be negated.

;;; A world-state; It comes before and after some action
;;; And contains a set of predicates true at that time



(defclass specialized-search-context ()
  ())

(defclass state (specialized-search-context)
  ((state-name :accessor state-name :initarg :state-name)
   (nicknames :accessor nicknames :initform nil :initarg :nicknames)
   (depth :accessor depth :initform 0 :initarg :depth)
   (predecessor :accessor predecessor :initarg :predecessor :initform nil)
   (successors :accessor successors :initarg :successors :initform nil)
   (prior-action :accessor prior-action :initarg :prior-action :initform nil)
   (next-action :accessor next-action :initarg :next-action :initform nil)
   (is-on-solution-path? :accessor is-on-solution-path? :initform nil)
   (intermediate-state? :accessor intermediate-state? :initform nil :initarg :intermediate-state?)
   ))

(defmethod print-object ((thing state) stream)
  (format stream "#<state ~a>" (state-name thing)))

(defparameter *initial-state* nil)
(defparameter *state-ht* (make-hash-table))

(defun clear-all-states ()
  (clrhash *state-ht*)
  (setf (successors *initial-state*) nil
	(gethash (state-name *initial-state*) *state-ht*) *initial-state*))

(defun make-initial-state ()
  (setq *initial-state* (make-instance 'state :state-name 'initial :depth 0))
  (setf (gethash (state-name *initial-state*) *state-ht*) *initial-state*))

(eval-when (:load-toplevel :execute)
  (make-initial-state))

(defun intern-state (state-identifier &optional (prior-state nil prior-state-supplied-p) nicknames)
  (when (eql state-identifier t) (break))
  ;; For both prior-state and state
  ;; we could be called with either a state-identifier or a state
  (let ((state nil))
    (typecase state-identifier
      (state (setq state state-identifier))
      (symbol
       (setq state (gethash state-identifier *state-ht*))
       (when (null state)
	 (setq state (make-instance 'state :state-name state-identifier))
	 (setf (gethash state-identifier *state-ht*) state)
	 (if prior-state-supplied-p 
	     (when (and (symbolp prior-state) (not (null prior-state)))
	       ;; if prior state is explictly NIL we don't want to intern 
	       ;; a state name NIL
	       (setq prior-state (intern-state prior-state)))
	   (setq prior-state *initial-state*))
	 (when prior-state
	   (push state (successors prior-state))
	   (setf (predecessor state) prior-state
		 (depth state) (1+ (depth prior-state))
		 )))))
    (loop for nickname in nicknames do (add-nickname state nickname))
    state))

(defun rename-state (state-identifier new-name)
  (let ((existing-state (if (symbolp state-identifier) (gethash state-identifier *state-ht*) state-identifier)))
    (when existing-state
      (remhash (state-name existing-state) *state-ht*)
      (setf (state-name existing-state) new-name)
      (setf (gethash new-name *state-ht*) existing-state))))

(defmethod add-nickname ((state-name symbol) new-name)
  (add-nickname (intern-state state-name) new-name))

(defmethod add-nickname ((state state) new-name)
  (push new-name (nicknames state))
  (setf (gethash new-name *state-ht*) state))

(defclass state-truth-map ()
  ((true-states :accessor true-states :initform nil :initarg :true-states)
   (false-states :accessor false-states :initform nil :initarg :false-states)))

(defmethod remove-state-from-truth-map ((state state) (truth-map state-truth-map))
  (setf (true-states truth-map) (remove state (true-states truth-map))
        (false-states truth-map) (remove state (false-states truth-map))))

(defparameter *truth-value-ht* (make-hash-table))
(defparameter *state-predicate-interning-ht* (make-hash-table))

(define-predicate-model stateful-predicate-mixin () ())

;;; Puts a new state between two existing states
;;; The new state can have an action that takes you from it to the
;;; existing successor.
;;; Extra credit: Update the nicknames 

(defun link-state (predecessor successor)
  (setf (predecessor successor) predecessor
        (successors predecessor) (list successor)
        (depth successor) (1+ (depth predecessor))))

(defun thread-state (existing-predecessor new-state existing-successor)
  (unless  (eql (predecessor existing-successor) existing-predecessor)
    (error "Threading between non-adjacent states ~a ~a ~a" 
           existing-predecessor existing-successor (predecessor existing-successor)))  
  (setf (predecessor new-state) (predecessor existing-successor)
        (successors new-state) (successors existing-predecessor))
  (let ((action (prior-action existing-successor)))
    (when action
      (setf (prior-action new-state) (prior-action existing-successor)
            (prior-action existing-successor) nil
            (next-state action) new-state))          )
  (setf (successors existing-predecessor) (list new-state)
        (predecessor existing-successor) new-state))

;;; This is called when an attempt to achieve a prerequisite for 
;;; a contemplated action fails.
;;; Take the original predecessor and sucessor states
;;; Kills all the states between and restores the action as the link
;;; between them.  
;;; Removes all action taken assertions mentioning the intermediate states

(defun unthread-state (predecessor successor)
  ;; if there's nothing in between there's nothing to do
  (unless (eql (predecessor successor) predecessor)
    (let ((intermediate-states nil))
      ;; we're assuming a linear chain of states and actions
      (loop for predecessor = predecessor then next-state
          for next-state = (first (successors predecessor))
          until (eql next-state successor)
          do (push next-state intermediate-states))
      (loop for state in intermediate-states do (kill-state state))
      (setf (successors predecessor) (list successor)
            (predecessor successor) predecessor)
      ;; remove any action taken assertions that link
      ;; to or from intermediate-states
      (ask `[action-taken ?predecessor ?successor] 
           #'(lambda (just)
               (when (or (member ?predecessor intermediate-states)
                         (member ?successor intermediate-states))
                 (untell (ask-database-predication just))))))))
        


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Non Stateful Predicates
;;;  Most predicates in the planner are termporally contigent
;;;  That is they are true only at certain points in time
;;;
;;;  But there are a lot of predicates that are Background Knowledge
;;;   and are not temporally contigent, they are always true and are
;;;   asserted in the starting environment of the planner
;;;   these are the non-stateful predicates
;;;
;;; These are compiled differenlty by def-attack-method and define-action in
;;; that they aren't embedded inside an in-state predication
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-predicate-model non-stateful-predicate-model () (ltms:ltms-predicate-model))

(define-predicate-method (after-clear stateful-predicate-mixin) (&optional (clear-database t) undefrules)
  (declare (ignore undefrules))
  (when clear-database
    (clrhash *truth-value-ht*)
    (clrhash *state-ht*)
    (clrhash *state-predicate-interning-ht*)
    (make-initial-state)
    ))

;;; This is for vanilla assertions other than things like current-foothold
;;; and has-been-visited. The pred that is returned is unique according to
;;; the standard protocol.
(define-predicate-method (tell stateful-predicate-mixin :around) (truth-value justification)
  (with-statement-destructured (internal-pred state) self
    (if (typep internal-pred 'ji:not-model)
      (with-statement-destructured (real-internal-pred) internal-pred
	(call-next-method `[,(predication-predicate self) ,real-internal-pred ,(intern-state state)] (negate-truth-value truth-value) justification))
      (call-next-method `[,(predication-predicate self) ,internal-pred ,(intern-state state)] truth-value justification))))

(define-predicate-method (insert stateful-predicate-mixin) ()
  (with-statement-destructured (internal-pred state) self    
    (let* ((canonical-state (intern-state state))
	   (canonicalized-internal-pred (insert internal-pred))
	   (canonicalized-pred `[,(predication-predicate self) ,canonicalized-internal-pred ,canonical-state])
	   (truth-map (gethash canonicalized-internal-pred *truth-value-ht*)))
      (unless truth-map 
	(setq truth-map (make-instance 'state-truth-map))
	(setf (gethash canonicalized-internal-pred *truth-value-ht*) truth-map))
      (let ((internal-pred-entry (gethash canonicalized-internal-pred *state-predicate-interning-ht*)))
	(unless internal-pred-entry
	  (setq internal-pred-entry (make-hash-table))
	  (setf (gethash canonicalized-internal-pred *state-predicate-interning-ht*) internal-pred-entry))
	(let ((interned-statement (gethash canonical-state internal-pred-entry)))
	  (cond
	   (interned-statement (values interned-statement nil))
	   (t (setf (gethash canonical-state internal-pred-entry) canonicalized-pred)
	      (values canonicalized-pred t))))))))

;;; When something gets untold this will get called to remove 
;;; all indexing information.  Just the dual of the above
(define-predicate-method (uninsert stateful-predicate-mixin :before) ()
  (with-statement-destructured (internal-pred state) self    
    (let* ((canonical-state (intern-state state))
           (canonicalized-internal-pred (insert internal-pred))
           (truth-map (gethash canonicalized-internal-pred *truth-value-ht*)))
      ;; remove this state from the truth-map of the internal-pred
      (when truth-map (remove-state-from-truth-map canonical-state truth-map))
      (let ((internal-pred-entry (gethash canonicalized-internal-pred *state-predicate-interning-ht*)))
        (when internal-pred-entry
          (remhash canonical-state internal-pred-entry))))))

(define-predicate-method (act-on-truth-value-change stateful-predicate-mixin) (old-truth-value &optional old-predication-state)
  (declare (ignore old-predication-state old-truth-value))
  (with-statement-destructured (internal-pred state) self
    ;; Note at this point the internal-pred is the canonical version
    ;; and the state is the interned state
    (let ((new-truth-value (predication-truth-value self))
	  (truth-map (gethash internal-pred *truth-value-ht*)))
      (cond
       ((eql new-truth-value +true+)
	(pushnew state (true-states truth-map)))
       ((eql new-truth-value +false+)
	(pushnew state (false-states truth-map)))))))

(define-predicate-method (ask stateful-predicate-mixin :around) (truth-value continuation do-backward-rules do-questions)
  (with-statement-destructured (internal-pred state) self
    ;; Some predications are immutable in which case we just ask about them
    (if (or (typep internal-pred 'non-stateful-predicate-model)
	    (typep internal-pred 'ji::named-part-of-mixin))
	(flet ((my-continuation (just)
		 (if (unbound-logic-variable-p state)
		   (with-unification
		    (unify state *initial-state*)
		    (funcall continuation just))
		 (funcall continuation just))
		 ))
	  (when (eql truth-value +false+) (setq truth-value (negate-truth-value truth-value)))
	  (ji:ask-internal internal-pred  truth-value #'my-continuation 
			   do-backward-rules do-questions))
      (call-next-method))))


(define-predicate-method (ask-data stateful-predicate-mixin) (truth-value continuation)
  (let ((query self))
    (with-statement-destructured (internal-pred state-descriptor) query
      ;; In some later version we can generalize to handle the 4 cases of
      ;; either/both/none of the internal-pred and state-descriptor are unbound.
      (labels
	  ((succeed (interned-internal-pred database-predication)
             ;; state is here for future expansion where it could be a variable
	     (with-unification 
	      (typecase interned-internal-pred
		(slot-value-mixin
                 ;; this is necessary because slot-value-mixin interns
                 ;; a pred with the slot vs the path.  I.e. source pred
                 ;; won't unify with one another.  Maybe that could be fixed
                 ;; at the unify predication level except that's not a generic function
                 ;; Note that the path part of the query can't have logic variables
                 ;; except for the first thing, which is a query to map over everything
                 ;; which we don't support here.  This means that follow-path works correctly here
                 ;; It's possible that the internal pred was just a logic variable which has been
                 ;; unified, but we need to dereference it in that case.
                 (with-statement-destructured (path value) (ji::joshua-logic-variable-value internal-pred)
                   (with-statement-destructured (his-path his-value) interned-internal-pred
                     (unify (follow-path path nil) his-path)
                     (unify his-value value))))
		(named-component
		 (typecase internal-pred
		   (value-of 
		    (with-statement-destructured (path value) internal-pred
		      (declare (ignore path))
		      (with-statement-destructured (parent name sub-object) interned-internal-pred
			(declare (ignore parent name))
			(unify value sub-object))))
		   (named-component
		    (with-statement-destructured (his-parent his-name value) internal-pred
		      (declare (ignore his-parent his-name))
		      (with-statement-destructured (parent name sub-object) interned-internal-pred
			(declare (ignore parent name))
			(unify value sub-object))))))
		(otherwise
		 (unify interned-internal-pred internal-pred)))
	      (stack-let ((backward-support (list query truth-value database-predication )))
		(funcall continuation backward-support))))
	   (handle-predicate (backward-support)
             ;; Succeed here should be called with a standard justification
             ;; since we're using ask-data with a truth-value of nil.
             ;; from that we get the the canonical version of the query predication.
             ;; But to figure out which that is we need to search the truth-map (since the query might
             ;; have a successor state of the one in which it was explicitly asserted
             ;; This is why we have to handle at the ask-data level rather than the fetch level
             ;; (since fetch doesn't get the truth-value).
	     (let* ((interned-internal-pred (ask-database-predication backward-support))
		    (truth-map (gethash interned-internal-pred *truth-value-ht*))
		    (false-states (when truth-map (false-states truth-map)))
		    (true-states (when truth-map (true-states truth-map)))
		    (negated (eql truth-value +false+)))
               ;; if the internal predication has never been told in a state 
               ;; But has been asserted in bare form
               ;; then just check
               ;; if it has the right truth-value
	       (cond
		((null truth-map)
		 (when (eql (predication-truth-value interned-internal-pred) truth-value)
		   (with-unification
		    (when (Unbound-logic-variable-p state-descriptor)
		      (unify *initial-state* state-descriptor))
		    (succeed interned-internal-pred interned-internal-pred))))
                ;; There's not a specific state specified
		((unbound-logic-variable-p state-descriptor)
		 (loop for winning-state in (if negated false-states true-states)
                     do (with-unification
                         (unify state-descriptor winning-state)
                         (succeed interned-internal-pred 
                                  (gethash winning-state (gethash interned-internal-pred *state-predicate-interning-ht*))))))
		(t
		 (loop for this-state = (intern-state state-descriptor) then (predecessor this-state)
		     until (null this-state)
		     if (or (and negated (member this-state false-states))
			    (and (not negated) (member this-state true-states))
                            ;; But if we get to the initial state we just check truth-values
			    (and (eql this-state *initial-state*)
				 (or  (and negated (eql (predication-truth-value interned-internal-pred) +false+))
				      (and (not negated) (eql (predication-truth-value interned-internal-pred) +true+)))))
                        ;; should build a justification
		     do (succeed interned-internal-pred 
				 (gethash this-state (gethash interned-internal-pred *state-predicate-interning-ht*)))
                        ;; if it doesn't hit in any state but does hit in the "base" environment
                        ;; and it has the right truth-value then succeed
		     finally (when (eql (predication-truth-value interned-internal-pred) truth-value)
			       (with-unification
				(unify state-descriptor *initial-state*)
				(succeed interned-internal-pred interned-internal-pred)))))))))
	(cond
	 ((unbound-logic-variable-p internal-pred)
	  (loop for interned-internal-pred being the hash-keys of *state-predicate-interning-ht*
	      do (with-unification
                  (unify internal-pred interned-internal-pred )
                  (stack-let ((backward-support (list self +true+ interned-internal-pred )))
                    (handle-predicate backward-support)))))
	 (t ;; handle negated internal predication
	  (when (typep internal-pred 'ji::not-model)
	    (setq internal-pred (second (predication-statement internal-pred))
		  truth-value (negate-truth-value truth-value)))
	  (ask-data internal-pred (if (typep internal-pred 'type-of-mixin) +true+ nil) #'handle-predicate)))))))

(define-predicate in-state (predication state) (stateful-predicate-mixin ltms:ltms-predicate-model))

(defun is-predecessor-of (state1 state2)
  (let ((target-depth (depth state1)))
    (loop for this-state = state2 then next-state
	for this-depth = (depth this-state)
	for next-state = (predecessor this-state)
	do (cond ((= this-depth target-depth)
		  (return-from is-predecessor-of (eql this-state state1)))
		 ((< this-depth target-depth)
		  (return-from is-predecessor-of nil)))
	until (null next-state))))

(defun state-of-pred (predication)
  (with-statement-destructured (embedded-pred state) predication
    (declare (ignore embedded-pred))
    state))

(defun depth-of-pred (predication)
  (depth (state-of-pred predication)))

(defun consistent-state (state-set)
  (cond 
   ((null (rest state-set)) (first state-set))
   (t
    (setq state-set (sort (copy-seq state-set) #'> :key #'depth))
    (loop for (first-state next-state . rest) on state-set by #'rest
        when (not (is-predecessor-of next-state first-state))
        do (return nil)
        when (null rest)
        return (first state-set)))))

(define-predicate consistent-state (result &rest state-set) (tell-error-model default-predicate-model))

(define-predicate-method (expand-forward-rule-trigger consistent-state) (support-variable-name truth-value context bound-variables)
  (declare (ignore context))
  (unless (eql truth-value +true+)
    (error 'ji:model-can-only-handle-positive-queries
	   :query self
	   :model (type-of self)))
  (with-predication-maker-destructured (final-variable &rest set) self
    `(:procedure 
      (let ((final-state (consistent-state (list ,@set))))
	(when final-state
	  (with-unification
	   (unify ,final-variable final-state)
	   (succeed nil))))
      ,support-variable-name
      ,bound-variables
      ,self)))

;;; An ask-data method for this just for completeness

(define-predicate-method (ask-data consistent-state) (truth-value continuation)
  (unless (eql truth-value +true+)
    (error 'ji:model-can-only-handle-positive-queries
       :query self
       :model (type-of self)))
  (with-statement-destructured (final-state . other-states) self
    (when (or (unbound-logic-variable-p final-state)
	      (loop for other-state in other-states
		  thereis (unbound-logic-variable-p other-state)))
    (error 'ji::model-cant-handle-query
	   :query self 
	   :model (type-of self)))
    (when (find-if #'unbound-logic-variable-p other-states)
      (error 'ji:model-cant-handle-query
	      :query self
	      :model (type-of self)))
    (let ((answer (consistent-state other-states)))
      (when answer
	(with-unification
	 (unify final-state answer)
	 (stack-let ((backward-support (list self +true+  '(ask-data consistent-state))))
	   (funcall continuation backward-support)
	   ))))))

;;; This needs to handle 3 cases:
;;; The trigger is non-stateful - just compile in the trigger
;;; The trigger is stateful and negate - compile in [not [in-state trigger state]]
;;; The trigger is stateful and not negated compile in [in-state trigger state]
;;; We don't have to do anything about negated stateful then-parts because tell handles 
;;; that.  And we assume that the then-part is always stateful.
;;; Would be nice to allow :if and :then just as defrule does

(defmacro define-fwrd-stateful-rule (name if if-part then then-part)
  (when (eql if 'then) (rotatef if-part then-part) (rotatef if then))
  (unless (and (or (eql if 'if) (eql if :if))
               (or (eql then 'then) (eql then :then)))
    (error "Must have if and then"))
  (destructuring-bind (pred . triggers) (predication-maker-statement if-part)
    (unless (eql pred 'and) (error "Must have and for trigger"))
    (loop for trigger in triggers
        for trigger-pred = (predication-maker-predicate trigger)
        for trigger-is-negated = (eql trigger-pred 'not)
        for real-trigger-pred = (if trigger-is-negated (predication-maker-predicate (second (predication-maker-statement trigger)))
                                  trigger-pred)
        for is-non-stateful = (subtypep real-trigger-pred 'non-stateful-predicate-model)
	for state-variable = `(logic-variable-maker ,(gentemp "?STATE-"))
	for real-trigger = (cond (is-non-stateful trigger)
                                 ((and (not is-non-stateful) trigger-is-negated)
                                  `(predication-maker '(not (predication-maker '
                                                             (in-state ,(second (predication-maker-statement trigger)) ,state-variable)))))
                                 (t `(predication-maker '(in-state ,trigger ,state-variable))))
	collect real-trigger into real-triggers
        when (not is-non-stateful)
	collect state-variable into state-variables
	finally ;; (break "~a ~a" real-triggers state-variables)
	  (let* ((final-state-variable `(logic-variable-maker ,(gentemp "?FINAL-STATE-")))
		 (consistent-state-trigger `(predication-maker '(consistent-state ,final-state-variable ,@state-variables)))
		 (real-if-part `(predication-maker '(and ,@(append real-triggers (list consistent-state-trigger)))))
		 (real-then-part `(predication-maker '(in-state ,then-part ,final-state-variable))))
	    (return `(defrule ,name (:forward) if ,real-if-part then ,real-then-part))))))

(defmethod mark-state-useful ((state state))
  (setf (is-on-solution-path? state) t)
  (let ((prior-action (prior-action state))
	(intermediate-state? (intermediate-state? state)))
    (cond
     (prior-action
      (setf (is-on-solution-path? prior-action) t)
      (let ((prior-state (prior-state prior-action)))
	(when prior-state
	  (mark-state-useful prior-state))))
     (intermediate-state?
      (let ((prior-state (predecessor state)))
	(when prior-state
	  (mark-state-useful prior-state)))
      ))))

(defun kill-state (state)
  ;; kill all actions leading to a useless state
  (ask `[action-taken ?action ?input-state ,state]
       #'(lambda (backward-support)
           (let ((predication (ask-database-predication backward-support)))
             ;; kill all consequences which are the predications in 
             ;; the useless state
             (loop for consequence in (consequences predication)
                 do (untell consequence))
             (untell predication))))
  )

(defun clear-useless-states ()
  (labels ((do-one (state)
	     (let ((successors (successors state))
		   (useful-successors nil))
	       (loop for successor in successors
		   do (do-one successor)
		 if (is-on-solution-path? successor)
		   do (push successor useful-successors)
                   else do (kill-state successor))
	       (setf (successors state) useful-successors))))
    (do-one *initial-state*)))

(defun state-trace (final-state)
  (nreverse 
    (loop for state = final-state then next-state
	for next-state = (predecessor state)
	collect state
	until (null next-state)
	      )))

(defun action-sequence (final-state)
  (setq final-state (intern-state final-state))
  (nreverse
   (loop for state = final-state then prior-state
       for action = (prior-action state)
       for prior-state = (predecessor state)
       when action
       collect action
       until (null prior-state))))

(defun display-action-sequence (action-sequence &optional (stream *standard-output*))
  (loop for action in action-sequence
      for name = (name action)
      for args = (arguments action)
      do (format stream "~%~a ~{~a~^, ~}" name args)))


(defun predications-newly-in-state (state)
  (when (symbolp state) (setq state (intern-state state)))
  (let ((true-answers nil)
        (false-answers nil))
    (flet ((grabber (just truth)
             (let ((database-pred (ask-database-predication just)))
               (with-statement-destructured (internal-pred retrieved-state) database-pred
                 (case truth
                   (true (when (eql retrieved-state state) 
                           (push internal-pred true-answers)))
                   (false (when (eql retrieved-state state)
                            (push internal-pred false-answers))))))))
      (ask `[in-state ? ,state] #'(lambda (just) (grabber just 'true)))
      (ask `[not [in-state ? ,state]] #'(lambda (just) (grabber just 'false)))
      (append true-answers
              (mapcar #'(lambda (thing) `[not ,thing]) false-answers)))))


#|

(define-fwrd-stateful-rule mumble
    if [and [foo 1 2 3]
	    [foo 2 3 4]]
    then [foo 3 4 5])

(defrule mumble (:forward) 
  if [and [in-state [foo 1 2 3] ?state-1000] 
	  [in-state [foo 2 3 4] ?state-1001]
	  [consistent-state ?final-state-1002 ?state-1000 ?state-1001]]
  then [in-state [foo 3 4 5] ?final-state-1002])

A test case for backward rules
(define-predicate foo (a b))

(clear)
(intern-state 'state-1)
(intern-state 'state-2 'state-1)
(intern-state 'state-3 'state-1)

(tell [in-state [foo 1 2] state-1])
(tell [in-state [foo 2 3] state-2])

(defrule state-chain (:backward)
  then [in-state [foo ?a ?c] ?state]
  if [and (not (unbound-logic-variable-p ?a))
	  (not (unbound-logic-variable-p ?c))
	  [in-state [foo ?a ?b] ?state]
	  (not (unbound-logic-variable-p ?b))
	  [in-state [foo ?b ?c] ?state]]
  )

(ask [in-state [foo 1 3] state-2] #'print-query)

This works but then goes into an infinite loop looking for other matches to [in-state [foo 1 ?b] state-2] which triggers 
the same rule but not ?c is unbound.  This has nothing to do with "in-state" it's a classic case of transitivity rules
not working in the backward direction for example:

(defrule chain (:backward)
  then [foo ?a ?c]
  if [and [foo ?a ?b]
	  (not (unbound-logic-variable-p ?b))
	  [foo ?b ?c]]
  )


(tell [foo 1 2])
(tell [foo 2 3])

also goes into infinite loop after finding the answer

|#




;;; Todo: I think backward rules should just work because they depend on the ask-data method
;;;       But needs to be checked.
;;; Forward Rules:
;;;  Outline (defrule xx (:forward) IF [and [in-state ... ?x] [in-state ...  ?x]] ...
;;;    turns into If [and [in-state ... ?x1] [in-state ... ?x2] (consistent-states ?x1 ?x2 pred-1 pred-2)
;;;  Where consistent states gets the deepest state out of ?x1 ?x2 and then checks that for all the 
;;;  embdeded preds they are have the desired truth-values in that deepest state.
