{-# OPTIONS --safe #-}
module Data.Truncation.Set.Path where

open import Meta.Prelude

open import Meta.Effect.Map

open import Structures.n-Type

open import Data.Truncation.Propositional as ∥-∥₁
  using (∥_∥₁; ∣_∣₁)
open import Data.Truncation.Set.Base public
open import Data.Truncation.Set.Instances.Map
open import Data.Truncation.Set.Properties as ∥-∥₂

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  x y : A

instance opaque
  H-Level-∥-∥₂ : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n ∥ A ∥₂
  H-Level-∥-∥₂ ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 squash₂
  {-# OVERLAPPING H-Level-∥-∥₂ #-}

@0 =∘∣-∣₂≃∥-∥₁∘=
  : {x y : A}
  → ∣ x ∣₂ ＝ ∣ y ∣₂
  ≃ ∥ x ＝ y ∥₁
=∘∣-∣₂≃∥-∥₁∘= {A} {x} {y} = prop-extₑ! (encode x ∣ y ∣₂) (decode x (∣ y ∣₂)) where
  Code : (x : A) (y : ∥ A ∥₂) → Prop _
  Code x = elim! (λ y → el! ∥ x ＝ y ∥₁)

  encode : ∀ x y → ∣ x ∣₂ ＝ y → ⌞ Code x y ⌟
  encode x y = Jₚ (λ y _ → ⌞ Code x y ⌟ ) ∣ refl ∣₁

  decode : ∀ x y → ⌞ Code x y ⌟ → ∣ x ∣₂ ＝ y
  decode x = elim! λ _ → ap ∣_∣₂

ae : A ≃ B → ∥ A ∥₂ ≃ ∥ B ∥₂
ae e = to , is-iso→is-equiv (iso from ri li)
  where
  module e = Equiv e
  to = map e.to
  from = map e.from

  ri : from is-right-inverse-of to
  ri = elim! (ap ∣_∣₂ ∘ e.ε)

  li : from is-left-inverse-of to
  li = elim! (ap ∣_∣₂ ∘ e.η)
