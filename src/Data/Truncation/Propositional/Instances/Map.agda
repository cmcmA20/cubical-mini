{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Instances.Map where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Inductive

open import Data.Truncation.Propositional.Base

instance
  private
    H-Level-∥-∥₁ : ∀ {n ℓ} {A : Type ℓ} → H-Level (suc n) ∥ A ∥₁
    H-Level-∥-∥₁ = hlevel-prop-instance squash₁

  Map-∥-∥₁ : Map (eff ∥_∥₁)
  Map-∥-∥₁ .map f = rec! (∣_∣₁ ∘ f)

  Lawful-Map-∥-∥₁ : Lawful-Map (eff ∥_∥₁)
  Lawful-Map-∥-∥₁ .Lawful-Map.map-pres-id {A} = fun-ext go where opaque
    go : (x : ∥ A ∥₁) → map refl x ＝ x
    go = elim! λ _ → refl
  Lawful-Map-∥-∥₁ .Lawful-Map.map-pres-comp {A} {f} {g} = fun-ext go where opaque
    go : (x : ∥ A ∥₁) → map (f ∙ g) x ＝ (map f ∙ map g) x
    go = elim! λ _ → refl
