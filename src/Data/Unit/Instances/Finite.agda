{-# OPTIONS --safe #-}
module Data.Unit.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.Fin.Computational.Closure
open import Data.List.Base
open import Data.Unit.Properties

open import Truncation.Propositional.Base

instance
  ⊤-is-bishop-finite : is-bishop-finite ⊤
  ⊤-is-bishop-finite = fin₁ ∣ (is-contr→equiv-⊤ fin-1-is-contr) ₑ⁻¹ ∣₁

  decomp-fin-⊤ : goal-decomposition (quote is-bishop-finite) ⊤
  decomp-fin-⊤ = decomp (quote ⊤-is-bishop-finite) []
