;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

(define-recipe-object-type container)
(define-recipe-object-type container-with-contents)

(define-recipe-object-type receptacle)

(define-recipe-object-type bowl
    :super-types (receptacle))

(define-recipe-object-type utensil)

(define-recipe-object-type fork
    :super-types  (utensil))

(define-recipe-object-type spatula
    :super-types (utensil))

(define-recipe-object-type cooking-utensil
    :super-types (utensil)
    :slots ((temperature))
    )

(define-recipe-object-type skillet
    :super-types (cooking-utensil))

(define-recipe-object-type appliance
    )

(define-recipe-object-type heat-source
    :super-types (appliance)
    :slots ((switch-position)))

(define-recipe-object-type cook-top
    :super-types (heat-source)
    )

(define-recipe-object-type liquid)

(define-recipe-object-type solid)

(define-recipe-object-type food)

(define-recipe-object-type egg-white
    :super-types (liquid food))

(define-recipe-object-type egg-yolk
    :super-types (liquid food))

(define-recipe-object-type set-of-stuff
    :slots ((constituent :set-valued t)))

(define-recipe-object-type set-of-liquids
    :super-types (set-of-stuff))

(define-recipe-object-type egg-contents
    :parts ((yolk egg-yolk)
            (whites egg-white)))

(defun tell-about-egg-contents (the-egg)
  (let ((shell (follow-path (list the-egg 'shell)))
        (insides (follow-path (list the-egg 'insides))))
    (tell `[contains ,shell ,insides])))

(define-recipe-object-type egg
    :super-types (food container-with-contents)
    :parts ((shell container)
            (insides egg-contents))
    :initializations ((tell-about-egg-contents self))
    )

(define-recipe-object-type ham
    :super-types (food solid)
    )

(define-recipe-object-type cheese
    :super-types (food solid)
    )

(define-recipe-object-type mixture
    :slots ((components :set-valued t)))

(define-recipe-object-type liquid-mixture
    :super-types (mixture liquid))

(define-recipe-object-type solid-mixture
    :super-types (mixture solid))

(define-recipe-object-type person
    )

(define-recipe-object-type cook
    :super-types (person)
    )

(define-recipe-object-type recipe
    )



(define-fwrd-stateful-rule hold-not-hand-empty
    ;; the macro insists that the trigger is conjunctive
    if [and [holding ?actor ?thing]]
    then [not [handempty ?actor]])

(define-fwrd-stateful-rule have-ingredient
  if [and [ingredient-of ?recipe ?thing]
          [cook-of ?recipe ?the-cook]]
  then [has ?the-cook ?thing]
  )

(define-fwrd-stateful-rule have-utensil
  if [and [utensil-of ?recipe ?thing]
          [cook-of ?recipe ?the-cook]]
  then [has ?the-cook ?thing]
  )

(define-fwrd-stateful-rule have-appliance
  if [and [appliance-of ?recipe ?thing]
          [cook-of ?recipe ?the-cook]]
  then [has ?the-cook ?thing]
  )

(define-fwrd-stateful-rule ham-omelet
    if [and [object-type-of ?m liquid-mixture]
            [is-folded ?m]
            [object-type-of ?h ham]
            [constituent-of ?h ?m]
            [object-type-of ?c cheese]
            [constituent-of ?c ?m]]
    then [is-prepared ?m ham-and-cheese-omelet])




(defun make-eggs ()
  (clear)
  (let ((the-eggs (make-object 'egg :name 'the-eggs))
        (the-cook (make-object 'cook :name 'the-cook))
        (the-ham (make-object 'ham :name 'the-ham))
        (the-cheese (make-object 'cheese :name 'the-cheese))
        (the-recipe (make-object 'recipe :name 'the-recipe))
        (the-bowl (make-object 'bowl :name 'the-bowl))
        (the-fork (make-object 'fork :name 'the-fork))
        (the-spatula (make-object 'spatula :name 'the-spatula))
        (the-skillet (make-object 'skillet :name 'the-skillet))
        (the-cook-top (make-object 'cook-top :name 'the-cook-top))
        (the-insides-of-the-eggs (follow-path '(the-eggs insides)))
        the-mixture)
    ;; (tell `[in-state [value-of (,the-skillet temperature) :unknown] initial])
    (tell `[in-state [handempty ,the-cook] initial])
    (tell `[in-state [ingredient-of ,the-recipe ,the-eggs] initial])
    (tell `[in-state [ingredient-of ,the-recipe ,the-ham] initial])
    (tell `[in-state [ingredient-of ,the-recipe ,the-cheese] initial])
    (tell `[in-state [utensil-of ,the-recipe ,the-bowl] initial])
    (tell `[in-state [utensil-of ,the-recipe ,the-fork] initial])
    (tell `[in-state [utensil-of ,the-recipe ,the-skillet] initial])
    (tell `[in-state [utensil-of ,the-recipe ,the-spatula] initial])
    (tell `[in-state [appliance-of ,the-recipe ,the-cook-top] initial])
    (tell `[in-state [cook-of ,the-recipe ,the-cook] initial])

    ;; Break eggs into receptacle
    (do-action 'break-eggs-into-receptacle 'initial 'before-break-eggs 'after-break-eggs the-cook the-eggs the-bowl)

    ;; Stir
    (do-action 'stir-eggs 'after-break-eggs 'before-stir 'after-stir the-cook the-insides-of-the-eggs the-bowl the-fork)
    (let ((the-action (prior-action (intern-state 'after-stir))))
      (setq the-mixture (named-output the-action 'the-mixture)))

    ;; Pour
    (do-action 'pour-into-hot-skillet 'after-stir 'before-pour 'after-pour the-cook the-mixture the-bowl the-skillet)

    ;; Fry
    (do-action 'fry-eggs 'after-pour 'before-fry 'after-fry the-cook the-mixture the-skillet the-cook-top)

    ;; Add Ham
    (do-action 'add-ingredient 'after-fry 'before-add-ham 'after-add-ham the-cook the-ham the-mixture)

    ;; Add cheese
    (do-action 'add-ingredient 'after-add-ham 'before-add-cheese 'after-add-cheese the-cook the-cheese the-mixture)

    ;; Fold
    (do-action 'fold 'after-add-cheese 'before-fold 'after-fold the-cook the-mixture the-spatula)
    ))
