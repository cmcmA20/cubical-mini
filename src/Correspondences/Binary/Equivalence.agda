{-# OPTIONS --safe #-}
module Correspondences.Binary.Equivalence where

open import Foundations.Base
open import Foundations.HLevel

open import Correspondences.Base
open import Correspondences.Binary.Reflexive
open import Correspondences.Binary.Symmetric
open import Correspondences.Binary.Transitive

-- only homogeneous for now

record Equivalence {ℓᵃ} {A : 𝒰 ℓᵃ} {ℓ}
  (_~_ : Corr² (A , A) ℓ) : 𝒰 (level-of-type A ⊔ ℓ) where
  field instance
    reflexive  : Reflexive _~_
    symmetric  : Symmetric _~_
    transitive : Transitive _~_

record is-congruence {ℓᵃ} {A : 𝒰 ℓᵃ} {ℓ}
  (_~_ : Corr² (A , A) ℓ) : 𝒰 (level-of-type A ⊔ ℓ) where
  field
    equivalence : Equivalence _~_
    has-prop    : ∀ {x y} → is-prop (x ~ y)

  opaque instance
    H-Level-~ : ∀ {n x y} → H-Level (suc n) (x ~ y)
    H-Level-~ = hlevel-prop-instance has-prop

  open Equivalence equivalence public
