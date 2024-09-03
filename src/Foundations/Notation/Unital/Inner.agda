{-# OPTIONS --safe #-}
module Foundations.Notation.Unital.Inner where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Transitivity

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓl ℓr : Level}
  (L : A → B → 𝒰 ℓl) (R : B → B → 𝒰 ℓr) where

  Unitality-i : (r : Reflexivity R) (t : Transitivity L R L) → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓl)
  Unitality-i r t = {x : A} {y : B} (p : L x y) → t p r ＝ p

  record Unit-i ⦃ r : Refl R ⦄ ⦃ t : Trans L R L ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓl ⊔ ℓr) where
    no-eta-equality
    field ∙-id-i : Unitality-i (r .refl) (t ._∙_)

open Unit-i ⦃ ... ⦄ public

Unit-iʰ : (R : A → A → 𝒰 ℓ) ⦃ r : Refl R ⦄ ⦃ t : Transʰ R ⦄ → Type _
Unit-iʰ R = Unit-i R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where

  Unitality-rᵘ : (r : A) (t : A → A → A) → 𝒰 ℓᵃ
  Unitality-rᵘ r t = (x : A) → t x r ＝ x

  record Unit-rᵘ ⦃ r : Reflᵘ A ⦄ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field <>-id-r : Unitality-rᵘ (r .mempty) (t ._<>_)

open Unit-rᵘ ⦃ ... ⦄ public

instance
  Unit-rᵘ→Unit-i
    : ⦃ _ : Reflᵘ A ⦄ ⦃ _ : Transᵘ A ⦄ ⦃ _ : Unit-rᵘ A ⦄
    → Unit-i {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Unit-rᵘ→Unit-i .∙-id-i = <>-id-r
  {-# INCOHERENT Unit-rᵘ→Unit-i #-}
