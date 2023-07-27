{-# OPTIONS --safe #-}
module Data.Quotient.Type.Base where

open import Foundations.Base

data _/_ {ℓ ℓ′} (A : Type ℓ) (R : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  ⦋_⦌ : (a : A) → A / R
  eq/ : (a b : A) (r : R a b) → ⦋ a ⦌ ＝ ⦋ b ⦌

private variable
  ℓᵃ ℓᵇ ℓʳ ℓᵖ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  P : A → Type ℓᵖ
  R : A → A → Type ℓʳ

elim
  : (f : Π[ a ꞉ A ] P ⦋ a ⦌)
  → (∀ a b (r : R a b) → ＜ f a ／ (λ i → P (eq/ a b r i)) ＼ f b ＞)
  → Π[ q ꞉ A / R ] P q
elim f _  ⦋ a ⦌ = f a
elim f f= (eq/ a b r i) = f= a b r i

rec : (f : A → B)
    → (∀ a b → R a b → f a ＝ f b)
    → A / R → B
rec = elim
