{-# OPTIONS --safe #-}
module Data.Empty.Instances.Finite where

open import Foundations.Base

open import Meta.Finite

open import Data.Empty.Base
open import Data.Fin.Closure

open import Truncation.Propositional.Base

instance
  Finite-⊥ : Finite ⊥
  Finite-⊥ .Finite.cardinality = 0
  Finite-⊥ .Finite.enumeration = ∣ fin-0-is-initial ₑ⁻¹ ∣₁
