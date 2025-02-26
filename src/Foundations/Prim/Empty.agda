{-# OPTIONS --safe #-}
module Foundations.Prim.Empty where

open import Foundations.Prim.Type

private variable ℓ : Level

data ⊥ₜ : Type where

elim : {B : ⊥ₜ → Type ℓ} → (x : ⊥ₜ) → B x
elim ()

rec : {A : Type ℓ} → ⊥ₜ → A
rec = elim
