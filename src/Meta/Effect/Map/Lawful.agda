{-# OPTIONS --safe #-}
module Meta.Effect.Map.Lawful where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map.Base

private variable ℓᵃ ℓᵇ ℓᶜ : Level

record Lawful-Map (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ has-map ⦄ : Map M
    map-pres-id
      : {A : Type ℓᵃ}
      → map refl ＝ the (M.₀ A → M.₀ A) refl
    map-pres-comp
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
        {f : A → B} {g : B → C}
      → map (f ∙ g) ＝ the (M.₀ A → M.₀ C) (map f ∙ map g)
