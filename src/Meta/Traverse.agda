{-# OPTIONS --safe #-}
module Meta.Traverse where

open import Foundations.Base

open import Meta.Idiom

record Traverse (F : Effect) : Typeω where
  private module F = Effect F
  field
    traverse
      : ∀ {ℓ₀ ℓ₁} {M : Effect} ⦃ i : Idiom M ⦄ (let module M = Effect M)
          {a : Type ℓ₀} {b : Type ℓ₁}
      → (a → M.₀ b) → F.₀ a → M.₀ (F.₀ b)
  for
    : ∀ {ℓ₀ ℓ₁} {M : Effect} ⦃ i : Idiom M ⦄ (let module M = Effect M)
        {a : Type ℓ₀} {b : Type ℓ₁}
    → F.₀ a → (a → M.₀ b) → M.₀ (F.₀ b)
  for x f = traverse f x

open Traverse ⦃ ... ⦄ public
