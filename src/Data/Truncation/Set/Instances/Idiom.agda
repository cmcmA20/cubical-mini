{-# OPTIONS --safe #-}
module Data.Truncation.Set.Instances.Idiom where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Map
open import Meta.Inductive

open import Data.Truncation.Set.Base
open import Data.Truncation.Set.Instances.Map public

private variable
  n : HLevel
  ℓ : Level
  A : Type ℓ

open Idiom ⦃ ... ⦄
open Lawful-Idiom ⦃ ... ⦄

instance
  private
    _ : H-Level (2 + n) ∥ A ∥₂
    _ = hlevel-basic-instance 2 squash₂

  Idiom-∥-∥₂ : Idiom (eff ∥_∥₂)
  Idiom-∥-∥₂ .pure = ∣_∣₂
  Idiom-∥-∥₂ ._<*>_ ∣f∣₂ ∣a∣₂ = rec! (_<$> ∣a∣₂) ∣f∣₂

  Lawful-Idiom-∥-∥₂ : Lawful-Idiom (eff ∥_∥₂)
  Lawful-Idiom-∥-∥₂ .pure-id {A} {v} = go v where opaque
    go : (x : ∥ A ∥₂) → (pure id <*> x) ＝ x
    go = elim! λ _ → refl
  Lawful-Idiom-∥-∥₂ .pure-pres-app = refl
  Lawful-Idiom-∥-∥₂ .pure-interchange {A} {B} {u} {v} = go u v where opaque
    go : (f : ∥ (A → B) ∥₂) (x : A) → (f <*> pure x) ＝ (pure (_$ x) <*> f)
    go = elim! (λ _ _ → refl)
  Lawful-Idiom-∥-∥₂ .pure-comp {A} {B} {C} {u} {v} {w} = go u v w where opaque
    go : (g : ∥ (B → C) ∥₂) (f : ∥ (A → B) ∥₂) (x : ∥ A ∥₂)
       → (pure _∘ˢ_ <*> g <*> f <*> x) ＝ (g <*> (f <*> x))
    go = elim! (λ _ _ _ → refl)
  Lawful-Idiom-∥-∥₂ .map-pure = fun-ext (elim! λ _ → refl)
