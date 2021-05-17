;;; -*- Mode: Common-lisp; Package: recipes; Readtable: Joshua -*-

(in-package :recipes)

(define-action basic-break (?actor ?victim)
  :prerequisites ([has ?actor ?victim])
  :post-conditions ([broken ?victim])
  :typing ((?victim container-with-contents))
  :abstract t
  )

(define-action break-eggs-into-receptacle (?receptacle)
  :super-types (basic-break)
  :prerequisites ([holding ?actor ?victim]
                  [above ?victim ?receptacle]
                  [has ?actor ?victim]
                  [has ?actor ?receptacle]
                  )
  :post-conditions ([in ?victim.insides ?receptacle]
                    [broken ?victim.shell]
                    [not [in ?victim.insides ?victim.shell]]
                    [value-of (?the-mixture constituent) ?victim.insides.whites]
                    [value-of (?the-mixture constituent) ?victim.insides.yolk]  
                    [not [holding ?actor ?victim]]
                    [handempty ?actor]
                    )
  :typing ((?actor cook)
           (?victim egg)
           (?receptacle receptacle))
  :outputs ((?the-mixture set-of-liquids egg-contents))
  )
             

(define-action stir-liquids (?actor ?the-constituents ?receptacle ?utensil)
  :prerequisites ([in ?the-constituents ?receptacle]
                  [has ?actor ?receptacle]
                  [has ?actor ?utensil]
                  )
  :outputs ((?the-mixture liquid-mixture the-mixture))
  :typing ((?the-constituents set-of-liquids))
  :post-conditions ([constituent-of ?the-eggs.yolk ?the-mixture]
                    [constituent-of ?the-eggs.whites ?the-mixture]
                    [in ?the-mixture ?receptacle]))
  
(define-action stir-eggs (?actor ?the-eggs ?receptacle ?utensil)
  :prerequisites ([in ?the-eggs ?receptacle]
                  [has ?actor ?receptacle]
                  [has ?actor ?utensil]
                  )
  :outputs ((?the-mixture liquid-mixture the-mixture))
  :typing ((?the-eggs egg-contents))
  :post-conditions ([constituent-of ?the-eggs.yolk ?the-mixture]
                    [constituent-of ?the-eggs.whites ?the-mixture]
                    [in ?the-mixture ?receptacle])
  )


(define-action pour-into-hot-skillet (?actor ?source ?source-container ?receptacle)
  :prerequisites ([in ?source ?source-container]
                  [has ?actor ?receptacle]
                  [value-of ?receptacle.temperature hot])
  :post-conditions ([in ?source ?receptacle]
                    [not [in ?source ?source-container]])
  )

(define-action fry-eggs (?actor ?mixture ?receptacle ?heat-source)
  :prerequisites ([in ?mixture ?receptacle]
                  [value-of ?receptacle.temperature hot]
                  [value-of ?heat-source.switch-position high]
                  )
  :post-conditions ([state-of ?mixture ?fried]
                    [is-flexible ?mixture])
  )

(define-action add-ingredient (?actor ?ingredient ?something)
  :typing ((?actor cook)
           (?ingredient food)
           (?something mixture))
  :prerequisites ([has ?actor ?ingredient])
  :post-conditions ([constituent-of ?ingredient ?something]))

(define-action fold (?actor ?thing ?instrument)
  :prerequisites ([has ?actor ?instrument]
                  [is-flexible ?thing])
  :post-conditions ([is-folded ?thing])
  )




(Define-action heat-cooking-utensil (?actor ?cooking-utensil ?cook-top)
  :typing ((?actor cook)
           (?cooking-utensil cooking-utensil)
           (?cook-top cook-top))
  :prerequisites ([has ?actor ?cooking-utensil]
                  [has ?actor ?cook-top])
  :post-conditions ([value-of ?cooking-utensil.temperature hot]
                    [value-of ?cook-top.switch-position high]))

(define-action pickup (?actor ?victim)
  :typing ((?actor cook))
  :prerequisites ([has ?actor ?victim]
                  [handempty ?actor]
                  )
  :post-conditions ([holding ?actor ?victim]))

(define-action move-over (?actor ?held-thing ?object)
  :typing ((?actor cook))
  :prerequisites ([has ?actor ?held-thing]
                  [has ?actor ?object]
                  [holding ?actor ?held-thing])
  :post-conditions ([above ?held-thing ?object]))


  
