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

(defun process-assertions (name assertions input-state)
  (labels ((do-one (assertion)
	     (cond
	       ;; special cases for debugging
	       ((and (listp assertion) (not (predication-maker-p assertion)) (eql (first assertion) :break))
		`(prog1 t (break ,@(rest assertion))))
               ((and (listp assertion) (not (predication-maker-p assertion)) (eql (first assertion) :trace))
                `(prog1 t (when *method-tracing*
                            (format t "~%~vtIn ~a, " (* 2 ji::*rule-depth*) ',name)
                            (format t ,@(rest assertion)))))
	       ((and (listp assertion) (predication-maker-p assertion) (eql (predication-maker-predicate assertion) 'or))
	        (with-predication-maker-destructured (&rest assertions) assertion
		  (loop for assertion in assertions
		        collect (do-one assertion) into processed-assertions
		        finally (return `(predication-maker '(or ,@processed-assertions))))))
	       ((and (listp assertion) (not (predication-maker-p assertion))) assertion)
	       ((compile-without-state assertion) assertion)
	       (t `(predication-maker '(in-state ,assertion ,input-state))))))
    (loop for thing in assertions collect (do-one thing))))

(defun find-prereqs-that-mention-outputs (prereqs output-forms)
  (let ((output-prereqs nil)
        (real-prereqs nil)
        (output-lvs nil))
    (loop for (lv nil nil) in output-forms
        do (pushnew lv output-lvs :test #'eql :key #'ji::logic-variable-maker-name))
    (loop for prereq in prereqs
        if (lvs-occurs-in output-lvs prereq)
        do (push prereq output-prereqs)
        else do (push prereq real-prereqs))
    (values real-prereqs output-prereqs)))

(defun process-guards (name assertions input-state) (process-assertions name assertions input-state))

(defun is-pretty-binding (assertion)
  (cond
   ((and (predication-maker-p assertion)
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
    t)
   ((listp assertion)
    (and (logic-variable-maker-p (first assertion))
         (eql (length assertion) 2)))
   (t nil)))


(defun de-prettify-binding (assertion)
  (flet ((process-path (list-of-strings)
           (loop for thing in list-of-strings
               if (char-equal (aref thing 0) #\?)
               collect (ji::make-logic-variable-maker (intern thing))
               else collect (intern thing))))
    (cond
     ((predication-maker-p assertion)
      (with-predication-maker-destructured  (path logic-variable) assertion
        (if (logic-variable-maker-p path)
            (let* ((name (logic-variable-maker-name path))
                   (exploded-path (explode-string name #\.))
                   (real-path (cons (ji::make-logic-variable-maker (intern (first exploded-path)))
                                    (process-path (rest exploded-path)))))
              (ji:make-predication-maker `(value-of ,real-path ,logic-variable)))
          (let ((expanded-path (process-path (explode-string path #\.))))
            (ji:make-predication-maker `(value-of ,expanded-path ,logic-variable))))))
     ((and (listp assertion) (eql (length assertion) 2) (logic-variable-maker-p (first assertion)))
      (destructuring-bind (logic-variable path) assertion
        (if (logic-variable-maker-p path)
            (let* ((name (logic-variable-maker-name path))
                   (exploded-path (explode-string name #\.))
                   (real-path (cons (ji::make-logic-variable-maker (intern (first exploded-path)))
                                    (process-path (rest exploded-path)))))
              (ji:make-predication-maker `(value-of ,real-path ,logic-variable)))
          (let ((expanded-path (process-path (explode-string path #\.))))
            (ji:make-predication-maker `(value-of ,expanded-path ,logic-variable)))))))))

(defun process-bindings (name assertions input-state)
  (let ((expanded-bindings (loop for assertion in assertions
			       collect (if (is-pretty-binding assertion)
					   (de-prettify-binding assertion)
					 assertion))))
    (process-assertions name expanded-bindings input-state)))

(defun process-prerequisites (name assertions input-state) (process-assertions name assertions input-state))

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

;;; For ASIST this wants to be object-type-of
;;; For interpreting Gary's stuff instance-of
(defparameter *typing-predicate* 'object-type-of)

(defun process-typing (name forms)
  (loop for form in forms
      if (and (listp form) (eql (first form) :break))
      collect `(prog1 t (break ,@(rest form)))
      else if (and (listp form) (eql (first form) :trace))
      collect `(prog1 t (when *method-tracing*
                          (format t "~%~vtIn ~a, " (* 2 ji::*rule-depth*) ',name)
                          (format t ,@(rest form))))
      else if (and (listp form) (= (length form) 2))
      collect (destructuring-bind (thing type) form
                (ji:make-predication-maker `(object-type-of ,thing ,type)))
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

(define-predicate take-action (name action input-state output-state) (ltms:ltms-predicate-model))
(define-predicate action-taken (action input-state output-state) (ltms:ltms-predicate-model))
(define-predicate check-prerequisites (name action input-state) (ltms:ltms-predicate-model))
(define-predicate prerequisite-satisfied (action-description prereq input-state) (ltms:ltms-predicate-model))
(define-predicate prerequisite-missing (action-description prereq input-state) (ltms:ltms-predicate-model))
;; name and inputs are in fact outputs, i.e. they are bound by invoking a rule
(define-predicate action-and-inputs-to-achieve-condition (predication output-state name inputs) (ltms:ltms-predicate-model))

(defun link-action (action prior-state next-state)
  ;; mainly for debugging if you pass in a list of
  ;; the name and the arguments, then we'll
  ;; create the action argument
  (when (listp action)
    (destructuring-bind (name . arguments) action
      (setq action (make-instance 'action
                     :role-name name
                     :name name
                     :name name
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

(defun pure-name-of-logic-variable-maker (lv-maker)
  (let* ((name (ji::logic-variable-maker-name lv-maker))
         (package (symbol-package name)))
    (intern (subseq (string name) 1) package)))

(defun process-new-outputs (variable-list action-variable output-state-variable)
  (let ((done-lvs nil))
    (loop for (lv . plist) in variable-list
        for type-for-creation = (getf plist :type-for-creation)
        for form-for-creation = (getf plist :form-for-creation)
        for additional-types = (getf plist :additional-types)
        for name = (getf plist :name)
        for real-name = (cond ((and (null name) type-for-creation) (make-name type-for-creation))
                              ((not (null name)) name)
                              (t (pure-name-of-logic-variable-maker lv)))
        unless (member lv done-lvs :test #'equal)
        collect (cond
                 ((and (null form-for-creation) (null type-for-creation)) `(unify ,lv ',real-name))
                 (type-for-creation `(unify ,lv (make-object ',type-for-creation :name ',real-name)))
                 (form-for-creation `(unify ,lv ,form-for-creation)))
        and collect `(let ((the-output (joshua-logic-variable-value ,lv))
                           (the-action (joshua-logic-variable-value ,action-variable)))
                       ,@(when additional-types
                           (loop for type in additional-types
                               collect `(tell [in-state [instance-of ,lv ,type] ,output-state-variable])))
                       ;; In the case where a new object is created
                       ;; (as opposed to just a symbol which is what Gary's format gives me)
                       ;; then the name and the object are a symbol and an object respectively
                       ;; But in the case of Gary's format there's just a symbol
                       ;; and these 2 are the same.  Nobody actually uses this as far as I can
                       ;; tell
                       (push (list ',real-name the-output) (outputs the-action)))
        do (push lv done-lvs))))

(defparameter *all-actions* nil)

(defun lv-thing-name (thing)
  (cond
   ((logic-variable-maker-p thing) (logic-variable-maker-name thing))
   ((unbound-logic-variable-p thing) (logic-variable-name thing))
   (t thing)))

(defun lvs-occurs-in (lv-makers form)
  (labels ((do-one (thing)
             (cond
              ((ji::logic-variable-maker-p thing)
               (if (member thing lv-makers :test #'equal)
                   (return-from lvs-occurs-in t)))
              ((symbolp thing))
              ((numberp thing))
              (t (loop for sub-thing in thing
                     do (do-one sub-thing))))))
    (do-one form)))

;;; Documentation for the outputs keyword:
;;; It means to create a new object in the output state
;;; Each element is a triple: (lv form alternative-type)
;;; there are 3 different usages:
;;; 1) A single type is provided, in that case make an object of that type
;;; 2) A form is provided, in that case the form is used to make the object (not sure this is ever used)
;;; 3) No 2nd argument is provide.  Just bind the lv to a symbol and assert that the symbol has the type
;;;    there may be several such forms with the same lv.
;;; Reason for all this: In Gary's dump format he might specify a new output and assert that it has several
;;; types.  In his usage, I don't use the object modelling capabilities but instead have explicit type-of and part of assertions
;;; In normal usage I do use the object modelling capabilities.
;;; The syntax should be cleared up with a lv and then keyword arguments.
;;; Maybe something like: :creation-type <xxx>, :creation-form <(xxx)>, :name <xxx>, :additional-types <(x, y, z)>

(defun mentioned-in? (lv-maker set-of-forms)
  (let ((name (if (symbolp lv-maker) lv-maker (logic-variable-maker-name lv-maker))))
    (labels ((in? (form)
               (cond
                ((logic-variable-maker-p form)
                 (if (eql name (logic-variable-maker-name form))
                     (return-from mentioned-in? t)
                   nil))
                ((predication-maker-p form)
                 (loop for term in (predication-maker-statement form)
                     do (in? term)))
                ((listp form)
                 (loop for term in form do (in? term)))
                ((eql name form)
                 (return-from mentioned-in? t))
                (t nil))))
      (in? set-of-forms))))

(defclass usage-record ()
  ((variable-name :accessor variable-name :initarg :variable-name)
   (ref :accessor ref :initarg :ref :initform nil)
   (def :accessor def :initarg :def :initform nil)))

(defmethod print-object ((record usage-record) stream)
  (format stream "#<usage ~a ref ~a def ~a>" (variable-name record) (ref record) (def record)))

(eval-when (:compile-toplevel :load-toplevel)
  (defparameter *set-names* '(head bindings guards prerequisites plan post-conditions)))

(defmacro compiler-warn (format-string &rest args)
  #+allegro
  `(compiler::warn ,format-string ,@args)
  #+sbcl
  `(sb-c:compiler-style-warn  ,format-string ,@args))

(defun find-all-variables (set-of-stuff tag already-seen output-variables)
  (let ((answers nil))
    (labels ((do-one (stuff &optional predication-maker)
               (cond
                ((predication-maker-p stuff)
                 (do-one (predication-maker-statement stuff) (unless (eql tag 'head) stuff)))
                ((logic-variable-maker-p stuff)
                 (let ((string-of-name (string (logic-variable-maker-name stuff))))
                   (unless (search "anonymous" string-of-name :test #'string-equal)
                     (let* ((first-dot (position #\. string-of-name :test #'char-equal))
                            (symbol (if first-dot
                                        (intern (subseq string-of-name 0 first-dot))
                                      (intern string-of-name)))
                            (entry (find symbol answers :key #'variable-name))
;;;                            (abstract-variable (when predication-maker (corresponding-abstract-variable predication-maker stuff)))
;;;                            (predicate (when predication-maker (predication-maker-predicate predication-maker)))
;;;                            (is-output? (or (eql tag 'head)
;;;                                            (when predication-maker (lookup-predicate-output-variable predicate abstract-variable))))
;;;                            (is-new-locally (null entry))
                            )
                       ;; (format t "~%Var ~a Pred maker ~a Pred ~a Abs-var ~a Output? ~a" symbol predication-maker predicate abstract-variable is-output?)
                       (unless entry
                         (setq entry (make-instance 'usage-record :variable-name symbol))
                         (push entry answers))
                       ;; Maybe the logic should be simpler:
                       ;; Except for the head
                       ;; Any 2nd mention is a ref, Any 1st mention is a def
                       ;; For any normal predicate this seems true, it will bind the unbound variables.
                       ;; when pattern matching.
                       (cond
                        ((member symbol already-seen)
                         ;; a 2nd mention of an variable that is an output-variable of the predicate
                         ;; that's already defined in this set is taken to be a reference
                         ;; (unless (and (def entry) is-new-locally)
                         ;;   (setf (ref entry) t))
                         (if (member symbol output-variables :key #'logic-variable-maker-name)
                             (setf (def entry) t)
                           (setf (ref entry) t))
                         )
                        (t (push symbol already-seen)
                           ;; (if is-output?
                           ;;     (setf (def entry) t)
                           ;;   (setf (ref entry) t))
                           (cond ((eql tag 'head)
                                  (if (member symbol output-variables :key #'logic-variable-maker-name)
                                      (setf (ref entry) t)
                                    (setf (def entry) t)))
                                 (t (setf (def entry) t)))
                           ))))))
                ((and (listp stuff) (= (length stuff) 2) (eql tag 'bindings) (logic-variable-maker-p (first stuff))
                      (null (find #\. (string (logic-variable-maker-name (first stuff))))))
                 (let* ((name (logic-variable-maker-name (first stuff)))
                        (entry (find name answers :key #'variable-name)))
                   (unless entry
                     (setq entry (make-instance 'usage-record :variable-name name :def t))
                     (push entry answers))
                   (push name already-seen))
                 (do-one (rest stuff)) predication-maker)
                ((listp stuff)
                 (loop for thing in stuff do (do-one thing predication-maker))))))
      (do-one set-of-stuff))
    (values (list tag answers)
            already-seen)))


(defun build-usage-map (head bindings typing prerequisites post-conditions output-variables)
  ;; Do we really want to ignore the typing
  ;; or do we want to treat it as a usage
  ;; (declare (ignore typing))
  (let ((alist nil) (all-refs nil))
    (macrolet ((do-one (name)
                 `(multiple-value-bind (entry updated-all-ref)
                      (find-all-variables ,name ',name all-refs output-variables)
                    (push entry alist)
                    (setq all-refs updated-all-ref))))
      (do-one head)
      (do-one bindings)
      (do-one prerequisites)
      (do-one typing)
      (do-one post-conditions))
  alist))

;;; The head is special: Any ref in the head should be def'd in the body
;;; All others anything def'd should be checked against all followers plus the head.
;;; Fix: I use compiler::warn here which is the right thing for ACL, need to shadow warn
;;; and import the right thing as warn for each implementation (mainly S-BCL).
(defun perform-usage-checks (alist method &optional ignore-list)
  (let* ((head (second (assoc 'head alist)))
         (bindings (second (assoc 'bindings alist)))
         (typing (second (assoc 'typing alist)))
         (plan (second (assoc 'plan alist)))
         (guards (second (assoc 'guards alist)))
         (prerequisites (second (assoc 'prerequisites alist)))
         (post-conditions (second (assoc 'post-conditions alist)))
         (ignore-list (loop for lv in ignore-list collect (ji::logic-variable-maker-name lv))))
    (macrolet ((do-checks (set-name)
                 (let* ((position (position set-name *set-names*))
                        (before (subseq *set-names* 0 (1+ position)))
                        (after (subseq *set-names* position)))
                   `(loop for entry in ,set-name
                        for var = (variable-name entry)
                        for def = (def entry)
                        for ref = (ref entry)
                        do ,(cond
                             ((eql set-name 'head)
                              `(cond
                                (ref (unless (or def (check-for-over-sets var (list ,@after) 'def))
                                       (compiler-warn "In ~a, Variable ~a is referenced in the head but is not defined after"
                                                       method var)))
                                (def
                                    (unless (or ref (check-for-over-sets var (list typing ,@after) 'ref) (member var ignore-list))
                                       (compiler-warn "In ~a, Varable ~a is defined in the head but is not referenced after"
                                                       method var)))))
                             (t `(cond
                                  (ref (unless (or def (check-for-over-sets var (list ,@before) 'def))
                                         (compiler-warn "In ~a, Variable ~a is referenced in the ~a but is not defined earlier" method var ',set-name)))
                                  (def (unless (or ref (check-for-over-sets var (list head ,@after) 'ref) (member var ignore-list))
                                         (compiler-warn "In ~a, Variable ~a is defined in the ~a but is not used"
                                                        method var ',set-name))))))))))
      (labels ((check-for (variable-name set type)
                 (let ((entry (find variable-name set :key #'variable-name)))
                   (cond ((null entry) nil)
                         ((eql type 'def) (def entry))
                         ((eql type 'ref) (ref entry)))))
               (check-for-over-sets (variable-name sets type)
                 (loop for set in sets thereis (check-for variable-name set type)))
               (is-used (var)
                 (let ((used-in nil))
                   (loop for (set-name entries) in alist
                       for entry = (find var entries :key #'variable-name)
                       when (and entry (ref entry))
                       do (push set-name used-in))
                   used-in)))
        ;; 1) for variables in the head, make sure that all variables are referenced
        (do-checks head)
        ;; 2) for variables in bindings, if it's defined make sure it's referenced somewhere
        ;; if it's reference make sure it was defined in the head.or in another binding.
        (do-checks bindings)
        ;; 3) Variables referenced in the prereqs should have been defined in the head, bindings or another prereq
        ;;    Variables defined in the prereqs should be referenced in the plan, post-conditions or another prereq
        (do-checks guards)
        (do-checks prerequisites)
        ;; 4) Variable referenced in plan should have defined in head, bindings, prereqs, or plan
        ;;    Variables defined in the plan should be used in the plan or the post-conditions
        (do-checks plan)
        ;; 5) Variables referenced in the post-conditions should have been defined in head, bindings, prerequs, plan or post-conditions
        ;;    Variables defined in the post-conditions should be used in the post-conditions
        (do-checks post-conditions)
        (loop for var in ignore-list
            for used-in = (is-used var)
            when used-in
            do (compiler-warn "In ~a, variable ~a is ignored but it is used in ~{~a, ~^and ~}" method var used-in))
        ))))


(defun normal-binding? (form)
  (or (and (predication-maker-p form)
           (eql (predication-maker-predicate form) 'value-of))
      (and (listp form)
           (= (length form) 2)
           (logic-variable-maker-p (first form)))))

(defun substitute-hidden-bindings (set-of-stuff reference-alist)
  (labels ((do-one (form)
             (cond
              ((and (predication-maker-p form) (eql (predication-maker-predicate form) 'value-of))
               (with-predication-maker-destructured (slot value) form
                 (ji:make-predication-maker
                  (list (predication-maker-predicate form)
                        (explode slot #\.)
                        (do-one value)))))
              ((predication-maker-p form)
               (ji:make-predication-maker
                (loop for token in (predication-maker-statement form)
                    collect (do-one token))))
              ((and (logic-variable-maker-p form) (find #\. (string (logic-variable-maker-name form)) :test #'char-equal))
               (let* ((entry (assoc (logic-variable-maker-name form) reference-alist)))
                 (second entry)))
              ((logic-variable-maker-p form) form)
              ((listp form)
               (loop for token in form collect (do-one token)))
              ((and (symbolp form) (find #\. (string form) :test #'char-equal))
               (let* ((entry (assoc form reference-alist)))
                 (second entry)))
              (t form))))
    (do-one set-of-stuff)
    ))

(defun merge-and-substitute-hiDden-bindings (set-of-stuff reference-alist bindings-by-set-type set-type)
  ;; (break "~{~a~^, ~}~%~a~%~{~a~^,~}~%~a" set-of-stuff reference-alist bindings-by-set-type set-type)
  (let ((bindings-for-set-type (second (assoc set-type bindings-by-set-type))))
    (cond
      ((and (null reference-alist) (eql set-type 'bindings))
       (loop for thing in set-of-stuff
             if (normal-binding? thing)
               collect (de-prettify-binding thing)
             else collect thing))
      ((null reference-alist) set-of-stuff)
      ((and (null bindings-for-set-type) (eql set-type 'bindings))
       (loop for thing in set-of-stuff
             if (normal-binding? thing)
               collect (de-prettify-binding thing)
             else collect (substitute-hidden-bindings thing reference-alist)))
      ((null bindings-for-set-type)
       (substitute-hidden-bindings set-of-stuff reference-alist))
      (t (let ((already-emitted nil))
           ;; loop over the forms
           ;; for each check all the implicit bindings
           ;; and if it's already been emitted skip it
           ;; otherwise if it's in the form, emit it and remember that it's been emitted
           (loop for thing in set-of-stuff
               do (print thing)
                 append (loop for (implicit-binding lv) in bindings-for-set-type
                              when (and (mentioned-in? implicit-binding thing)
                                        (not (member lv already-emitted)))
                                collect (de-prettify-binding (ji:make-predication-maker `(value-of ,implicit-binding ,lv)))
                            and do (push lv already-emitted))
                 if (normal-binding? thing)
                   collect (de-prettify-binding thing)
               else collect (substitute-hidden-bindings thing reference-alist)))))))

(defmacro define-action (name inputs &key bindings prerequisites post-conditions (define-predicate t) super-types outputs output-variables typing abstract ignore)
  ;; capture what was typed in
  ;; this stuff isn't really used and leads to complexity and errors
  ;; nuke out for now.
  (let ((source-inputs inputs)
        (source-outputs outputs)
        (source-prerequisites prerequisites)
        (source-post-conditions post-conditions)
        (source-typing typing)
        (source nil))
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
    (setq source (generate-source name source-inputs source-prerequisites source-post-conditions source-outputs source-typing))
    (multiple-value-bind (early-typing late-typing)
        (loop for type in typing
            for variable = (first type)
            if (and (eql variable :break) (loop for var in (rest (rest type)) thereis (mentioned-in? var inputs)))
            collect type into early
            else when (and (mentioned-in? variable inputs)
                           (not (member (logic-variable-maker-name variable) outputs :key #'(lambda (thing) (logic-variable-maker-name (first thing)))))
                           (not (member (logic-variable-maker-name variable) output-variables :key #'logic-variable-maker-name)))
            collect type into early
            else collect type into late
            finally (return (values early late)))
      (multiple-value-bind (all-refs hidden-bindings-alist) (find-hidden-bindings prerequisites post-conditions late-typing bindings)
        (let (;; (bindings-for-prereqs nil)
              ;; (bindings-for-post-conditions nil)
              ;; (bindings-for-typing nil)
              ;; This is only to create the action-type object
              ;; which isn't used and has bugs
              ;; (raw-prerequisites (loop for prereq in prerequisites collect (if (predication-maker-p prereq) prereq `',prereq)))
              ;; (raw-post-conditions post-conditions)
              ;; (raw-inputs (mapcar #'lv-thing-name inputs))
              ;; (raw-outputs (loop for (name) in outputs collect (lv-thing-name name)))
              ;; (raw-output-typing (loop for (lv . plist) in outputs
              ;;                        for type-for-creation = (getf plist :type-for-creation)
              ;;                        for form-for-creation = (getf plist :form-for-creation)
              ;;                        for other-types = (getf plist :additional-types)
              ;;                        if type-for-creation collect (list lv type-for-creation)
              ;;                        else if form-for-creation collect (list lv form-for-creation)
              ;;                        else if other-types append (loop for type in other-types collect (list lv type))
              ;;                                                   ))
              ;; (raw-typing typing)
              )
          (let ((usage-map (build-usage-map inputs bindings typing prerequisites post-conditions output-variables)))
            (perform-usage-checks usage-map name ignore))
          ;; (multiple-value-setq (prerequisites post-conditions typing) (substitute-hidden-variables prerequisites post-conditions typing hidden-bindings-alist))
          ; (loop for (dotted-form lv) in (second (assoc 'prerequisites hidden-bindings-alist))
          ;     do (push (ji:make-predication-maker `(value-of ,dotted-form ,lv)) bindings-for-prereqs))
          ; (loop for (dotted-form lv) in (second (assoc 'typing hidden-bindings-alist))
          ;     do (push (ji:make-predication-maker `(value-of ,dotted-form ,lv)) bindings-for-typing))
          ; (loop for (dotted-form lv) in (second (assoc 'post-conditions hidden-bindings-alist))
          ;     do (push (ji:make-predication-maker `(value-of ,dotted-form ,lv)) bindings-for-post-conditions))
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
                ;; this is here in an attempt to deal with the stuff Gary produces from Impact.
                ;; Probably that should be dealt with in the translation from Impact to actions
                (multiple-value-bind (real-prereqs output-prereqs) (find-prereqs-that-mention-outputs prerequisites outputs)
                  (declare (ignore real-prereqs output-prereqs))
                  `(eval-when (:compile-toplevel :load-toplevel :execute)
                     (pushnew ',name *all-actions*)
                     ;; Not cleqr I actually need this for anythig other than to get
                     ;; the source cod from a super-type
                     ;; the part that produces actual logic-variables and predications
                     ;; doesn't seem to be used and it gives
                     ;; errors sometimes due to bug of not identifying all logic variables
                     ;; used in it.
                     ,(define-action-type-creator name
                          ;;      :prerequisites raw-prerequisites
                          ;;      :post-conditions raw-post-conditions
                          ;;      :inputs raw-inputs
                          ;;      :outputs raw-outputs
                          ;;      :output-typing raw-output-typing
                          ;;      :super-types super-types
                          ;;      :typing raw-typing
                          :source-inputs source-inputs
                          :source-outputs source-outputs
                          :source-typing source-typing
                          :source-prerequisites source-prerequisites
                          :source-post-conditions source-post-conditions
                          :abstract abstract)
                     (let ((new-action-type (create-action-object ',name)))
                       (thread-action-type new-action-type))
                     ,source
                     ,@(when define-predicate `((define-predicate ,name ,names (,@super-types ltms:ltms-predicate-model))))
                     ,(generate-prereq-checker name inputs
                                               (process-typing name early-typing)
                                               (merge-and-substitute-hidden-bindings (process-bindings name bindings input-state-variable) all-refs hidden-bindings-alist 'bindings)
                                               (merge-and-substitute-hidden-bindings (process-typing name late-typing) all-refs hidden-bindings-alist 'typing)
                                               (merge-and-substitute-hidden-bindings prerequisites all-refs hidden-bindings-alist 'prerequisites)
                                               input-state-variable)
                     ,@(unless abstract (generate-prereq-achievers name logic-variables post-conditions (process-typing name typing)))
                     (defrule ,rule-name (:backward)
                       then [take-action ,name ?action ,@state-logic-variables]
                       if [and (let ((arguments (arguments ?action)))
                                 ;; unpack the arguments from the action object
                                 ,@(loop for lv in logic-variables
                                       collect `(unify ,lv (pop arguments)))
                                 t)
                               ,@(process-typing name early-typing)
                               ,@(merge-and-substitute-hidden-bindings (process-bindings name bindings input-state-variable) all-refs hidden-bindings-alist 'bindings)
                               ,@(merge-and-substitute-hidden-bindings (process-typing name late-typing) all-refs hidden-bindings-alist 'typing)
                               ,@(merge-and-substitute-hidden-bindings (process-prerequisites name prerequisites input-state-variable) all-refs hidden-bindings-alist 'prerequisites)
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
                                   ,@(process-new-outputs outputs action-variable output-state-variable)
                                   ,@(let* ((mnemonic (intern (string-upcase (format nil "action-taken-~A" name))))
                                            (justification-2 `(list ',mnemonic (list action-taken-pred))))
                                       (merge-and-substitute-hidden-bindings (process-post-conditions post-conditions output-state-variable justification-2)
                                                                             all-refs hidden-bindings-alist 'post-conditions))
                                   ))
                               ]))
                  )))))))
    ))




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

(defun find-hidden-bindings (prerequisites post-conditions typing bindings)
  (let ((bindings-by-set-type nil) (master-alist nil))
    (labels ((do-one (form set-type)
               (cond
                ((and (predication-maker-p form)
                      (eql (predication-maker-predicate form) 'value-of))
                 (when  (not (eql set-type 'bindings))
                   ;; don't scan value-of forms if we're doing bindings
                   (with-predication-maker-destructured (slot value) form
                     (declare (ignore value))
                     (do-one slot set-type))))
                ((predication-maker-p form)
                 (do-one (predication-maker-statement form) set-type))
                ((logic-variable-maker-p form)
                 (do-one (logic-variable-maker-name form) set-type))
                ((and (listp form) (= (length form) 2) (eql set-type 'bindings))
                 ;; if it's the short syntax and we're doing bindings, then do nothing
                 )
                ((listp form)
                 (loop for token in form do (do-one token set-type)))
                ((and (symbolp form) (find #\. (string form) :test #'char-equal))
                 ;; master-alist holds bindings across everything to avoid duplication
                 ;; Bindings-By-Set-Type is an Alist set-typeed by the name of the set.  It only
                 ;; gets an entry if this was a new symbol
                 (let ((entry (assoc set-type bindings-by-set-type)))
                   (unless entry
                     (setq entry (list set-type nil))
                     (push entry bindings-by-set-type))
                   (unless (member form master-alist :key #'first :test #'equal)
                     ;; it's a new symbol
                     (let ((pair (list form (ji:make-logic-variable-maker (make-name '?lv)))))
                       ;; add it to the master alist
                       (push pair master-alist)
                       ;; and to the alist of new entries for this set-type
                       (push pair (second entry)))))))))
      (loop for binding in bindings do (do-one binding 'bindings))
      (loop for type in typing do (do-one type 'typing))
      (Loop for prereq in prerequisites do (do-one prereq 'prerequisites))
      (loop for postcon in post-conditions do (do-one postcon 'post-conditions))
      )
    ;; Reverse the entries so that they are in the order of occurence
    (loop for entry in bindings-by-set-type
        do (setf (second entry) (nreverse (second entry))))
    (values master-alist bindings-by-set-type)))



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

(defun generate-prereq-checker (name logic-variables early-typeing bindings typing prerequisites input-state-logic-variable)
  `(defrule ,(smash "-" name 'check-prerequisites) (:backward)
     then [check-prerequisites ,name ?action ,input-state-logic-variable]
     if [and (let ((arguments (arguments ?action)))
               ,@(loop for lv in logic-variables
                     collect `(unify ,lv (pop arguments)))
               t)
             ,@early-typeing
             ,@bindings
             ,@typing
             ,@(loop for raw-prereq in prerequisites
                   collect `(check-one-prerequisite ',name ?action ,raw-prereq ,input-state-logic-variable))]))

;;; The workhorse for the rule generated above
;;; Notice the juggling that goes on if the prerequisite is negated
;;; You have to ask [not [in-state xxx] state] as opposed to [in-state [not xxx] state]
;;; Note: This assumes that all prerequisites are stateful
(defun check-one-prerequisite (name action prerequisite input-state)
  (declare (ignore name))
  (etypecase prerequisite
    (predication
     (let* ((found-it nil)
            (prerequisite-cant-be-told (typep prerequisite 'tell-error-model))
            (prerequisite-is-negated (typep prerequisite 'ji::not-model))
            (prerequisite-is-non-stateful (typep prerequisite 'non-stateful-predicate-model))
            (thing-to-be-told (cond
                               (prerequisite-cant-be-told nil)
                               (prerequisite-is-non-stateful prerequisite)
                               (prerequisite-is-negated `[not [in-state ,(second (predication-statement prerequisite)) ,input-state]])
                               (t `[in-state ,prerequisite ,input-state])))
        ;;; I could probably do this with forward rules, but the TMS hacking is more direct and less overhead
            (stateful-pred (if prerequisite-cant-be-told prerequisite (tell thing-to-be-told :justification :none)))
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
    (boolean (when prerequisite
               (values t nil nil)))
    ))

;;; A convenience function for scripting.  Just invokes the method
;;; which in turn invokes the function above.
(defun check-prerequisites (action state)
  (when (symbolp state)
    (setq state (intern-state state)))
  (let ((name (name action)))
    (ask* `[check-prerequisites ,name ,action ,state]
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

(defun do-action (name previous-output-state input-state output-state &rest arguments)
  (when (symbolp previous-output-state) (setq previous-output-state (intern-state previous-output-state nil)))
  (when (symbolp input-state) (setq input-state (intern-state input-state nil)))
  (when (symbolp output-state) (setq output-state (intern-state output-state input-state nil)))
  ;; Link input state to previous output-state with null action
  ;; this will cause predication inheritance from previous states
  (link-state previous-output-state input-state)
  (let ((action (make-instance 'action :name name :role-name (make-name name) :arguments arguments)))
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
    (ask* `[take-action ,name ,action ,input-state ,output-state]
          ))
  output-state)

#|

(defun take-action (action input-state output-state)
  (when (symbolp input-state) (setq input-state (intern-state input-state)))
  (cond ((null output-state) (setq output-state (intern-state (make-name 'output) input-state)))
        ((symbolp output-state) (setq output-state (intern-state output-state input-state))))
  (let ((name (name action)))
    (ask* `[take-action ,name ,action ,input-state ,output-state]
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
