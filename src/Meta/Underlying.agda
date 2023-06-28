{-# OPTIONS --safe #-}
module Meta.Underlying where

open import Foundations.Base

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ using (⌞_⌟) public

{-# DISPLAY Underlying.⌞_⌟ f x = ⌞ x ⌟ #-}

instance
  Underlying-Σ
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
    → ⦃ ua : Underlying A ⦄
    → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .Underlying.ℓ-underlying = ua .Underlying.ℓ-underlying
  Underlying-Σ .⌞_⌟ x = ⌞ x .fst ⌟
