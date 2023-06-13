{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.HLevel where

open import Foundations.Base

open import Meta.HLevel.Base

open import Truncation.Propositional.Base

instance
  H-Level-∥-∥₁ : ∀ {ℓ : Level} {A : Type ℓ} {n : HLevel} → H-Level (suc n) ∥ A ∥₁
  H-Level-∥-∥₁ = prop-instance squash₁
