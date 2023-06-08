{-# OPTIONS --safe #-}
module Data.Unit.Instances.Finite where

open import Foundations.Base

open import Meta.Finite

open import Data.Fin.Closure
open import Data.Unit.Properties

open import Truncation.Propositional.Base

instance
  Finite-⊥ : Finite ⊤
  Finite-⊥ .Finite.cardinality = 1
  Finite-⊥ .Finite.enumeration =
    ∣ (is-contr→equiv-⊤ fin-1-is-contr ∙ₑ lift-equiv {0ℓ}) ₑ⁻¹ ∣₁
