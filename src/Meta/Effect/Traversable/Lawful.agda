{-# OPTIONS --safe #-}
module Meta.Effect.Traversable.Lawful where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Effect.Idiom
open import Meta.Effect.Traversable

private variable ℓᵃ ℓᵇ ℓᶜ : Level

open Traversable ⦃ ... ⦄

record Lawful-Traversable (F : Effect) ⦃ f : Traversable F ⦄ : Typeω where
  private module F = Effect F
  open Map ⦃ ... ⦄
  open Idiom ⦃ ... ⦄
  field
   traverse-id : {A : Type ℓᵃ}
               → traverse ⦃ i = Idiom-Id ⦄ (id {A = A}) ＝ id
   traverse-comp : {M N : Effect}
                   ⦃ mi : Idiom M ⦄ (let module M = Effect M)
                   ⦃ ni : Idiom N ⦄ (let module N = Effect N)
                   ⦃ lm : Lawful-Idiom M ⦄ ⦃ ln : Lawful-Idiom N ⦄
                   {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
                   {f : A → M.₀ B} {g : B → N.₀ C}
                 → traverse ⦃ i = Idiom-Compose ⦄ (map g ∘ f) ＝
                   map (traverse g) ∘ traverse f
