{-# OPTIONS --safe #-}
module Meta.Effect.Traversable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map.Base
open import Meta.Effect.Idiom

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  M F : Effect

record Traversable (F : Effect) : Typeω where
  private module F = Effect F
  field
    traverse
      : ⦃ i : Idiom M ⦄ (let module M = Effect M)
      → (A → M.₀ B) → F.₀ A → M.₀ (F.₀ B)
  for
    : ⦃ i : Idiom M ⦄ (let module M = Effect M)
    → F.₀ A → (A → M.₀ B) → M.₀ (F.₀ B)
  for x f = traverse f x

open Map ⦃ ... ⦄
open Traversable ⦃ ... ⦄

-- aka dist
sequence
  : ⦃ _ : Idiom M ⦄ ⦃ _ : Traversable F ⦄
    (let module M = Effect M ; module F = Effect F)
  → F.₀ (M.₀ A) → M.₀ (F.₀ A)
sequence = traverse id

consume
  : ⦃ _ : Idiom M ⦄ ⦃ _ : Traversable F ⦄
    (let module M = Effect M ; module F = Effect F)
  → (F.₀ A → B) → F.₀ (M.₀ A) → M.₀ B
consume {M} f = map f ∘ sequence
