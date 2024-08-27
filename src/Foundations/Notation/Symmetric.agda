{-# OPTIONS --safe #-}
module Foundations.Notation.Symmetric where

open import Foundations.Prim.Type
open import Agda.Builtin.Unit

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) where

  Symmetry : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′)
  Symmetry = {x : A} {y : B} → I x y → O y x

  record Symm : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′) where
    no-eta-equality
    field sym : Symmetry

    -- TODO split these out + additive notation
    infix 90 _⁻¹
    _⁻¹ = sym
    infixl 60 _ᵒᵖ
    _ᵒᵖ = sym


open Symm ⦃ ... ⦄ public

Symmetric : (A → A → 𝒰 ℓ) → 𝒰 _
Symmetric R = Symm R R


-- "untyped" raw symmetry is just having an automorphism
record Symmᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field minv : A → A

open Symmᵘ ⦃ ... ⦄ public

instance
  Symmᵘ→Symm
    : ⦃ Symmᵘ A ⦄
    → Symm {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Symmᵘ→Symm .sym = minv
  {-# INCOHERENT Symmᵘ→Symm #-}
