{-# OPTIONS --safe #-}
module Truncation.Set.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Truncation.Set.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : A → Type ℓ′

instance
  decomp-hlevel-∥-∥₂ : goal-decomposition (quote is-of-hlevel) ∥ A ∥₂
  decomp-hlevel-∥-∥₂ = decomp (quote ∥-∥₂-is-of-hlevel) (`level-minus 2 ∷ [])
