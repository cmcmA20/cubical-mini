{-# OPTIONS --safe #-}
module Data.Empty.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.Empty.Base
open import Data.Fin.Computational.Closure
open import Data.List.Base

open import Truncation.Propositional.Base

instance
  ⊥-is-fin-set : is-fin-set ⊥
  ⊥-is-fin-set = fin₁ ∣ fin-0-is-initial ₑ⁻¹ ∣₁

  decomp-fin-⊥ : goal-decomposition (quote is-fin-set) ⊥
  decomp-fin-⊥ = decomp (quote ⊥-is-fin-set) []
