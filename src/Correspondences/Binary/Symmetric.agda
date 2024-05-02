{-# OPTIONS --safe #-}
module Correspondences.Binary.Symmetric where

open import Foundations.Prelude
  renaming (sym to symₚ)

open import Correspondences.Base

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

-- level-polymorphic, for automation
record Symm {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ : Level}
  (I : Corr² (A , B) ℓ) (O : Corr² (B , A) ℓ′) : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′) where
  no-eta-equality
  infix 90 _⁻¹
  field _⁻¹ : {x : A} {y : B} → I x y → O y x

  sym = _⁻¹

open Symm ⦃ ... ⦄ public

-- homogeneous
Symmetric : Corr² (A , A) ℓ → Type _
Symmetric R = Symm R R

instance
  Symm-Path : Symmetric (Path A)
  Symm-Path ._⁻¹ = symₚ

  Symm-≃ : Symm (_≃_ {ℓᵃ} {ℓᵇ}) _≃_
  Symm-≃ ._⁻¹ = _ₑ⁻¹

  Symm-≃ᴱ : Symm (_≃ᴱ_ {ℓᵃ} {ℓᵇ}) _≃ᴱ_
  Symm-≃ᴱ ._⁻¹ = _ᴱₑ⁻¹

  Symm-Iso : Symm (Iso {ℓᵃ} {ℓᵇ}) Iso
  Symm-Iso ._⁻¹ = _ᵢ⁻¹

-- "untyped" raw symmetry is just having an automorphism
record Symmᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field inv : A → A

open Symmᵘ ⦃ ... ⦄ public

instance
  Symmᵘ→Symm
    : ⦃ Symmᵘ A ⦄
    → Symm {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Symmᵘ→Symm ._⁻¹ = inv
  {-# INCOHERENT Symmᵘ→Symm #-}
