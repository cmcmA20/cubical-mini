{-# OPTIONS --safe #-}
module Foundations.Notation.Unital.Right where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Reflexive
open import Foundations.Notation.Transitive

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓl ℓr : Level}
  (L : A → B → 𝒰 ℓl) (R : B → B → 𝒰 ℓr) where

  Unitality-r : (r : Reflexivity R) (t : Transitivity L R L) → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓl)
  Unitality-r r t = {x : A} {y : B} (p : L x y) → t p r ＝ p

  record Unit-r ⦃ r : Refl R ⦄ ⦃ t : Trans L R L ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓl ⊔ ℓr) where
    field ∙-id-r : Unitality-r (r .refl) (t ._∙_)

open Unit-r ⦃ ... ⦄ public

Unital-right : (R : A → A → 𝒰 ℓ) ⦃ r : Reflexive R ⦄ ⦃ t : Transitive R ⦄ → Type _
Unital-right R = Unit-r R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where

  Unitality-rᵘ : (r : A) (t : A → A → A) → 𝒰 ℓᵃ
  Unitality-rᵘ r t = (x : A) → t x r ＝ x

  record Unit-rᵘ ⦃ r : Reflᵘ A ⦄ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    field <>-id-r : Unitality-rᵘ (r .mempty) (t ._<>_)

open Unit-rᵘ ⦃ ... ⦄ public

instance
  Unit-rᵘ→Unit-r
    : ⦃ _ : Reflᵘ A ⦄ ⦃ _ : Transᵘ A ⦄ ⦃ _ : Unit-rᵘ A ⦄
    → Unit-r {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Unit-rᵘ→Unit-r .∙-id-r = <>-id-r
  {-# INCOHERENT Unit-rᵘ→Unit-r #-}
