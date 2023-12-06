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
  ⊥-is-bishop-finite : is-bishop-finite ⊥
  ⊥-is-bishop-finite = fin₁ ∣ fin-0-is-initial ₑ⁻¹ ∣₁

  decomp-fin-⊥ : goal-decomposition (quote is-bishop-finite) ⊥
  decomp-fin-⊥ = decomp (quote ⊥-is-bishop-finite) []
