{-# OPTIONS --safe #-}
module Data.Empty.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.Empty.Base

instance
  decomp-hlevel-¬ : {ℓ : Level} {A : Type ℓ} → goal-decomposition (quote is-of-hlevel) (¬ A)
  decomp-hlevel-¬ = decomp (quote ¬-is-of-hlevel) (`level-minus 1 ∷ [])

  decomp-hlevel-⊥ : goal-decomposition (quote is-of-hlevel) ⊥
  decomp-hlevel-⊥ = decomp (quote ⊥-is-of-hlevel) (`level-minus 1 ∷ [])
