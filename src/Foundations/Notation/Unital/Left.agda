{-# OPTIONS --safe #-}
module Foundations.Notation.Unital.Left where

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
  (L : A → A → 𝒰 ℓl) (R : A → B → 𝒰 ℓr) where

  Unitality-l : (r : Reflexivity L) (t : Transitivity L R R) → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓr)
  Unitality-l r t = {x : A} {y : B} (q : R x y) → t r q ＝ q

  record Unit-l ⦃ r : Refl L ⦄ ⦃ t : Trans L R R ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓl ⊔ ℓr) where
    field ∙-id-l : Unitality-l (r .refl) (t ._∙_)

open Unit-l ⦃ ... ⦄ public

Unital-left : (R : A → A → 𝒰 ℓ) ⦃ r : Reflexive R ⦄ ⦃ t : Transitive R ⦄ → Type _
Unital-left R = Unit-l R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where

  Unitality-lᵘ : (r : A) (t : A → A → A) → 𝒰 ℓᵃ
  Unitality-lᵘ r t = (x : A) → t r x ＝ x

  record Unit-lᵘ ⦃ r : Reflᵘ A ⦄ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    field <>-id-l : Unitality-lᵘ (r .mempty) (t ._<>_)

open Unit-lᵘ ⦃ ... ⦄ public

instance
  Unit-lᵘ→Unit-l
    : ⦃ _ : Reflᵘ A ⦄ ⦃ _ : Transᵘ A ⦄ ⦃ _ : Unit-lᵘ A ⦄
    → Unit-l {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Unit-lᵘ→Unit-l .∙-id-l = <>-id-l
  {-# INCOHERENT Unit-lᵘ→Unit-l #-}
