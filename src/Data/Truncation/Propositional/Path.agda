{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Path where

open import Meta.Prelude

open import Meta.Effect.Map

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Instances.Map
open import Data.Unit.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  x y : A

instance opaque
  H-Level-∥-∥₁ : ∀ {n} → ⦃ n ≥ʰ 1 ⦄ → H-Level n ∥ A ∥₁
  H-Level-∥-∥₁ ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance squash₁
  {-# OVERLAPPING H-Level-∥-∥₁ #-}

ae : A ≃ B → ∥ A ∥₁ ≃ ∥ B ∥₁
ae {A} {B} e = ≅→≃ $ to , iso from ri li where
  to : ∥ A ∥₁ → ∥ B ∥₁
  to   = map (e    $_)
  from = map (e ⁻¹ $_)

  module e = Equiv e
  ri : from is-right-inverse-of to
  ri = elim! (ap ∣_∣₁ ∘ e.ε)

  li : from is-left-inverse-of to
  li = elim! (ap ∣_∣₁ ∘ e.η)
