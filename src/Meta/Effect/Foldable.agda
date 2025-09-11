{-# OPTIONS --safe #-}
module Meta.Effect.Foldable where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Choice
open import Meta.Effect.Alt
open import Meta.Effect.Map.Base
open import Meta.Effect.Idiom

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

record Foldable (F : Effect) : Typeω where
  private module F = Effect F
  field fold-r : (A → B → B) → B → F.₀ A → B
open Foldable ⦃ ... ⦄

open Choice ⦃ ... ⦄
open Alt ⦃ ... ⦄

asum : {F M : Effect} (let module F = Effect F; module M = Effect M)
       ⦃ f : Foldable F ⦄ ⦃ a : Alt M ⦄
     → F.₀ (M.₀ A) → M.₀ A
asum = fold-r _<|>_ fail

nondet
  : (F : Effect) {M : Effect} ⦃ f : Foldable F ⦄ ⦃ t : Map F ⦄
    ⦃ a : Alt M ⦄ ⦃ i : Idiom M ⦄
  → (let module F = Effect F; module M = Effect M)
  → F.₀ A → (A → M.₀ B) → M.₀ B
nondet F ⦃ f ⦄ xs k = asum ⦃ f ⦄ (k <$> xs)
