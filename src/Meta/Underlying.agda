{-# OPTIONS --safe #-}
module Meta.Underlying where

open import Foundations.Base

open import Data.Empty.Base

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ using (⌞_⌟) public

{-# DISPLAY Underlying.⌞_⌟ f x = ⌞ x ⌟ #-}

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : A → Type ℓ′
  P : Type ℓ′

instance
  Underlying-Σ : ⦃ ua : Underlying A ⦄ → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .Underlying.ℓ-underlying = ua .Underlying.ℓ-underlying
  Underlying-Σ .⌞_⌟ x = ⌞ x .fst ⌟

  Underlying-Type : Underlying (Type ℓ)
  Underlying-Type {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟ x = x

  Underlying-Lift : ⦃ ua : Underlying A ⦄ → Underlying (Lift ℓ′ A)
  Underlying-Lift ⦃ ua ⦄ .Underlying.ℓ-underlying = ua .Underlying.ℓ-underlying
  Underlying-Lift .⌞_⌟ x = ⌞ x .lower ⌟


infix 5 _∈_
_∈_ : ⦃ u : Underlying P ⦄ → A → (A → P) → Type _
x ∈ P = ⌞ P x ⌟

infix 5 _∉_
_∉_ : ⦃ u : Underlying P ⦄ → A → (A → P) → Type _
x ∉ P = ¬ x ∈ P

_⊆_ : ⦃ u : Underlying P ⦄ → (A → P) → (A → P) → Type _
U ⊆ V = {x : _} → x ∈ U → x ∈ V
