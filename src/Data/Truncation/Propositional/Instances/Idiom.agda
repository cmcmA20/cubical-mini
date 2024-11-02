{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Instances.Idiom where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Map
open import Meta.Inductive

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Instances.Map public

private variable
  n : HLevel
  ℓ : Level
  A : Type ℓ

instance
  private
    _ : H-Level (suc n) ∥ A ∥₁
    _ = hlevel-prop-instance squash₁

  Idiom-∥-∥₁ : Idiom (eff ∥_∥₁)
  Idiom-∥-∥₁ .pure = ∣_∣₁
  Idiom-∥-∥₁ ._<*>_ ∣f∣₁ ∣a∣₁ = rec! (_<$> ∣a∣₁) ∣f∣₁

  Lawful-Idiom-∥-∥₁ : Lawful-Idiom (eff ∥_∥₁)
  Lawful-Idiom-∥-∥₁ .pure-id {A} {v} = go v where opaque
    go : (x : ∥ A ∥₁) → (pure id <*> x) ＝ x
    go = elim! λ _ → refl
  Lawful-Idiom-∥-∥₁ .pure-pres-app = refl
  Lawful-Idiom-∥-∥₁ .pure-interchange {A} {B} {u} {v} = go u v where opaque
    go : (f : ∥ (A → B) ∥₁) (x : A) → (f <*> pure x) ＝ (pure (_$ x) <*> f)
    go = elim! (λ _ _ → refl)
  Lawful-Idiom-∥-∥₁ .pure-comp {A} {B} {C} {u} {v} {w} = go u v w where opaque
    go : (g : ∥ (B → C) ∥₁) (f : ∥ (A → B) ∥₁) (x : ∥ A ∥₁)
       → (pure _∘ˢ_ <*> g <*> f <*> x) ＝ (g <*> (f <*> x))
    go = elim! (λ _ _ _ → refl)
