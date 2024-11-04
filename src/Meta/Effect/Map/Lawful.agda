{-# OPTIONS --safe #-}
module Meta.Effect.Map.Lawful where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map.Base

private variable ℓᵃ ℓᵇ ℓᶜ : Level

open Map ⦃ ... ⦄

record Lawful-Map (M : Effect) ⦃ m : Map M ⦄ : Typeω where
  private module M = Effect M
  field
    map-pres-id
      : {A : Type ℓᵃ}
      → Path (M.₀ A → M.₀ A) (map refl) refl
    map-pres-comp
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
        {f : A → B} {g : B → C}
      → Path (M.₀ A → M.₀ C) (map (f ∙ g)) (map f ∙ map g)
