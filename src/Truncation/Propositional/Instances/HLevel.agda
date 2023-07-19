{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.List.Base

open import Truncation.Propositional.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : A → Type ℓ′

instance
  decomp-hlevel-∥-∥₁ : goal-decomposition (quote is-of-hlevel) ∥ A ∥₁
  decomp-hlevel-∥-∥₁ = decomp (quote ∥-∥₁-is-of-hlevel) (`level-minus 1 ∷ [])
