{-# OPTIONS --safe #-}
module Data.Truncation.Set.Instances.Map where

open import Foundations.Prelude

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Inductive

open import Data.Truncation.Set.Base

instance
  private
    H-Level-∥-∥₂ : ∀ {n ℓ} {A : Type ℓ} → H-Level (2 + n) ∥ A ∥₂
    H-Level-∥-∥₂ = hlevel-basic-instance 2 squash₂

  Map-∥-∥₂ : Map (eff ∥_∥₂)
  Map-∥-∥₂ .map f = rec! (∣_∣₂ ∘ f)

  Lawful-Map-∥-∥₂ : Lawful-Map (eff ∥_∥₂)
  Lawful-Map-∥-∥₂ .Lawful-Map.has-map = Map-∥-∥₂
  Lawful-Map-∥-∥₂ .Lawful-Map.map-pres-id =
    fun-ext (elim! λ _ → refl)
  Lawful-Map-∥-∥₂ .Lawful-Map.map-pres-comp =
    fun-ext (elim! λ _ → refl)
