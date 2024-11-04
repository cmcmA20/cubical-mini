{-# OPTIONS --safe #-}
module Meta.Effect.Bind.Lawful where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Bind.Base
open import Meta.Effect.Idiom

private variable ℓᵃ ℓᵇ ℓᶜ : Level

open Bind ⦃ ... ⦄
open Idiom ⦃ ... ⦄

record Lawful-Bind (M : Effect) ⦃ m : Bind M ⦄ : Typeω where
  private module M = Effect M
  field
    ⦃ has-lawful-idiom ⦄ : Lawful-Idiom M
    >>=-id-l
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {x : A} {f : A → M.₀ B}
      → (pure x >>= f) ＝ f x
    >>=-id-r
      : {A : Type ℓᵃ} {mx : M.₀ A}
      → (mx >>= pure) ＝ mx
    >>=-assoc
      : {A : Type ℓᵃ} {B : Type ℓᵇ} {C : Type ℓᶜ}
        {mx : M.₀ A} {f : A → M.₀ B} {g : B → M.₀ C}
      → (mx >>= f >>= g) ＝ (mx >>= λ x → f x >>= g)
