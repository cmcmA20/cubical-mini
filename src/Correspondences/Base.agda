{-# OPTIONS --safe #-}
module Correspondences.Base where

open import Foundations.Prelude

open import Meta.Underlying

open import Data.HVec.Base

-- Correspondence valued in arbitrary structure
SCorr
  : (arity : ℕ) {ls : Levels arity} (As : Types _ ls)
    {ℓ : Level} (U : Type ℓ) ⦃ u : Underlying U ⦄
  → Type (ℓ ⊔ ℓsup _ ls)
SCorr arity As U = Arrows arity As U

SCorr⁰ = SCorr 0
SCorr¹ = SCorr 1
SCorr² = SCorr 2
SCorr³ = SCorr 3
SCorr⁴ = SCorr 4
SCorr⁵ = SCorr 5

SPred = SCorr¹

-- Type-valued correspondence
Corr
  : (arity : ℕ) {ls : Levels arity} (As : Types _ ls) (ℓ : Level)
  → Type (ℓsuc ℓ ⊔ ℓsup _ ls)
Corr arity As ℓ = SCorr arity As (Type ℓ)

Corr⁰ = Corr 0
Corr¹ = Corr 1
Corr² = Corr 2
Corr³ = Corr 3
Corr⁴ = Corr 4
Corr⁵ = Corr 5

Pred = Corr¹
