{-# OPTIONS --safe #-}
module Foundations.Notation.Inverse.Right where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Reflexive
open import Foundations.Notation.Symmetric
open import Foundations.Notation.Transitive

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  (L : A → B → 𝒰 ℓ) (R : B → A → 𝒰 ℓ′) (O : A → A → 𝒰 ℓ″) where

  Invertibility-r : (r : Reflexivity O) (s : Symmetry L R) (t : Transitivity L R O ) → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ″)
  Invertibility-r r s t = {x : A} {y : B} (p : L x y) → t p (s p) ＝ r

  record Inv-r ⦃ r : Refl O ⦄ ⦃ s : Symm L R ⦄ ⦃ t : Trans L R O ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ″) where
    field ∙-inv-r : Invertibility-r (r .refl) (s .sym) (t ._∙_)

open Inv-r ⦃ ... ⦄ public

Inverse-right : (R : A → A → 𝒰 ℓ) ⦃ _ : Reflexive R ⦄ ⦃ _ : Symmetric R ⦄ ⦃ _ : Transitive R ⦄ → Type _
Inverse-right R = Inv-r R R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where
  Invertibility-rᵘ : (r : A) (s : A → A) (t : A → A → A) → 𝒰 ℓᵃ
  Invertibility-rᵘ r s t = (x : A) → t x (s x) ＝ r

  record Inv-rᵘ ⦃ r : Reflᵘ A ⦄ ⦃ s : Symmᵘ A ⦄ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    field <>-inv-r : Invertibility-rᵘ (r .mempty) (s .minv) (t ._<>_)

open Inv-rᵘ ⦃ ... ⦄ public

instance
  Inv-rᵘ→Inv-r
    : ⦃ _ : Reflᵘ A ⦄ ⦃ _ : Symmᵘ A ⦄ ⦃ _ : Transᵘ A ⦄ ⦃ _ : Inv-rᵘ A ⦄
    → Inv-r {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A) (λ _ _ → A)
  Inv-rᵘ→Inv-r .∙-inv-r = <>-inv-r
  {-# INCOHERENT Inv-rᵘ→Inv-r #-}
