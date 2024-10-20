{-# OPTIONS --safe #-}
module Cat.Functor.Equivalence where

open import Cat.Prelude
open import Cat.Functor.Properties

private variable
  o o′ h h′ : Level
  C D : Precategory o h
  F : Functor C D

open Functor

-- TODO conversions
module _ {C : Precategory o h} {D : Precategory o′ h′} where
  record is-precat-iso (F : Functor C D) : Type (o ⊔ o′ ⊔ h ⊔ h′) where
    no-eta-equality
    constructor make-precat-iso
    field
      has-ob-equiv : is-equiv-on-objects F
      has-ff       : is-fully-faithful F

unquoteDecl H-Level-is-precat-iso = declare-record-hlevel 1 H-Level-is-precat-iso (quote is-precat-iso)
