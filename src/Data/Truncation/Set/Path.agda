{-# OPTIONS --safe #-}
module Data.Truncation.Set.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Meta.Effect.Map

open import Structures.n-Type

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects
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
  b : Bool

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
  encode _ = J>! ∣ refl ∣₁

  decode : ∀ x y → ⌞ Code x y ⌟ → ∣ x ∣₂ ＝ y
  decode x = elim! λ _ → ap ∣_∣₂

instance
  Reflects-∣-∣₂=∣-∣₂ : ⦃ Reflects (x ＝ y) b ⦄ → Reflects (∣ x ∣₂ ＝ ∣ y ∣₂) b
  Reflects-∣-∣₂=∣-∣₂ = Reflects.dmap (ap ∣_∣₂) (λ x≠y p → ⊥.rec $ rec! x≠y $ =∘∣-∣₂≃∥-∥₁∘= $ p) auto

ae : A ≃ B → ∥ A ∥₂ ≃ ∥ B ∥₂
ae e = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li)
  where
  module e = Equiv e
  to = map e.to
  from = map e.from

  ri : from section-of′ to
  ri = elim! $ happly $ e.ε ▷ ∣_∣₂

  li : from retract-of′ to
  li = elim! $ happly $ sym $ e.η ▷ ∣_∣₂
