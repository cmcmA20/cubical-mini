{-# OPTIONS --safe #-}
module Foundations.Notation.Involutivity where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Symmetry

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) where

  Involutivity : (s₁ : Symmetry I O) (s₂ : Symmetry O I) → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ)
  Involutivity s₁ s₂ = {x : A} {y : B} (i : I x y) → s₂ (s₁ i) ＝ i

  record Invol ⦃ s₁ : Sym I O ⦄ ⦃ s₂ : Sym O I ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′) where
    no-eta-equality
    field sym-invol : Involutivity (s₁ .sym) (s₂ .sym)

open Invol ⦃ ... ⦄ public

Involʰ : (R : A → A → 𝒰 ℓ) ⦃ s : Symʰ R ⦄ → 𝒰 _
Involʰ R = Invol R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where
  Involutivityᵘ : (s : A → A) → 𝒰 ℓᵃ
  Involutivityᵘ s = (x : A) → s (s x) ＝ x

  record Involᵘ ⦃ s : Symᵘ A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field minv-invol : Involutivityᵘ (s .minv)

open Involᵘ ⦃ ... ⦄ public

instance
  Involᵘ→Invol
    : ⦃ s : Symᵘ A ⦄ ⦃ _ : Involᵘ A ⦄
    → Invol {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Involᵘ→Invol .sym-invol = minv-invol
  {-# INCOHERENT Involᵘ→Invol #-}
