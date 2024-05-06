{-# OPTIONS --safe #-}
module Foundations.Correspondences.Binary.Equivalence where

open import Foundations.Base
open import Foundations.HLevel

-- only homogeneous for now

record Equivalence {ℓᵃ} {A : 𝒰 ℓᵃ} {ℓ}
  (_~_ : A → A → 𝒰 ℓ) : 𝒰 (level-of-type A ⊔ ℓ) where
  field instance
    reflexive  : Reflexive  _~_
    symmetric  : Symmetric  _~_
    transitive : Transitive _~_

open Equivalence public

record is-congruence {ℓᵃ} {A : 𝒰 ℓᵃ} {ℓ}
  (_~_ : A → A → 𝒰 ℓ) : 𝒰 (level-of-type A ⊔ ℓ) where
  field
    equivalence : Equivalence _~_
    has-prop    : ∀ {x y} → is-prop (x ~ y)

  opaque instance
    H-Level-~ : ∀ {n x y} → H-Level (suc n) (x ~ y)
    H-Level-~ = hlevel-prop-instance has-prop
