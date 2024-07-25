{-# OPTIONS --safe #-}
module Foundations.Notation.Symmetric where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

-- level-polymorphic, for automation
record Symm {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′) where
  no-eta-equality
  infix 90 _⁻¹
  field _⁻¹ : {x : A} {y : B} → I x y → O y x

  sym = _⁻¹

open Symm ⦃ ... ⦄ public

-- homogeneous
Symmetric : (A → A → 𝒰 ℓ) → 𝒰 _
Symmetric R = Symm R R


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
