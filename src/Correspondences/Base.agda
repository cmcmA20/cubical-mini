{-# OPTIONS --safe #-}
module Correspondences.Base where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel

open import Meta.Variadic

open import Data.HVec.Base public

private variable
  ℓ ℓᵃ : Level
  A : Type ℓᵃ
  n : HLevel

-- Binary homogeneous correspondences

Reflexive : Corr² (A , A) ℓ → Type _
Reflexive _~_ = ∀ {x} → x ~ x

Symmetric : Corr² (A , A) ℓ → Type _
Symmetric _~_ = ∀ {x y} → (x ~ y) → (y ~ x)

Transitive : Corr² (A , A) ℓ → Type _
Transitive _~_ = ∀ {x y z} → (x ~ y) → (y ~ z) → (x ~ z)

record Equivalence (_~_ : Corr² (A , A) ℓ) : Type (level-of-type A ⊔ ℓ) where
  field
    reflᶜ : Reflexive _~_
    symᶜ  : Symmetric _~_
    _∙ᶜ_  : Transitive _~_

record is-congruence (_~_ : Corr² (A , A) ℓ) : Type (level-of-type A ⊔ ℓ) where
  field
    equivalenceᶜ : Equivalence _~_
    has-propᶜ : ∀ {x y} → is-prop (x ~ y)

  instance
    H-Level-~ : ∀ {x y} → H-Level (suc n) (x ~ y)
    H-Level-~ = hlevel-prop-instance has-propᶜ
  open Equivalence equivalenceᶜ public
