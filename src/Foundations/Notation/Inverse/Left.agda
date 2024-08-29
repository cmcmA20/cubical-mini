{-# OPTIONS --safe #-}
module Foundations.Notation.Inverse.Left where

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
  (R : A → B → 𝒰 ℓ) (L : B → A → 𝒰 ℓ′) (O : B → B → 𝒰 ℓ″) where

  Invertibility-l : (r : Reflexivity O) (s : Symmetry R L) (t : Transitivity L R O ) → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ″)
  Invertibility-l r s t = {x : A} {y : B} (p : R x y) → t (s p) p ＝ r

  record Inv-l ⦃ r : Refl O ⦄ ⦃ s : Symm R L ⦄ ⦃ t : Trans L R O ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ″) where
    field ∙-inv-l : Invertibility-l (r .refl) (s .sym) (t ._∙_)

open Inv-l ⦃ ... ⦄ public

Inverse-left : (R : A → A → 𝒰 ℓ) ⦃ _ : Reflexive R ⦄ ⦃ _ : Symmetric R ⦄ ⦃ _ : Transitive R ⦄ → Type _
Inverse-left R = Inv-l R R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where
  Invertibility-lᵘ : (r : A) (s : A → A) (t : A → A → A) → 𝒰 ℓᵃ
  Invertibility-lᵘ r s t = (x : A) → t (s x) x ＝ r

  record Inv-lᵘ ⦃ r : Reflᵘ A ⦄ ⦃ s : Symmᵘ A ⦄ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    field <>-inv-l : Invertibility-lᵘ (r .mempty) (s .minv) (t ._<>_)

open Inv-lᵘ ⦃ ... ⦄ public

instance
  Inv-lᵘ→Inv-l
    : ⦃ _ : Reflᵘ A ⦄ ⦃ _ : Symmᵘ A ⦄ ⦃ _ : Transᵘ A ⦄ ⦃ _ : Inv-lᵘ A ⦄
    → Inv-l {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A) (λ _ _ → A)
  Inv-lᵘ→Inv-l .∙-inv-l = <>-inv-l
  {-# INCOHERENT Inv-lᵘ→Inv-l #-}
