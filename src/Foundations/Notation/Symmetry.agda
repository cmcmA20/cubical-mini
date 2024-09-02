{-# OPTIONS --safe #-}
module Foundations.Notation.Symmetry where

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

  record Sym : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′) where
    no-eta-equality
    field sym : Symmetry

    -- TODO split these out + additive notation
    infix 90 _⁻¹
    _⁻¹ = sym
    infixl 60 _ᵒᵖ
    _ᵒᵖ = sym


open Sym ⦃ ... ⦄ public

Symʰ : (A → A → 𝒰 ℓ) → 𝒰 _
Symʰ R = Sym R R


-- "untyped" raw symmetry is just having an automorphism
record Symᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field minv : A → A

open Symᵘ ⦃ ... ⦄ public

instance
  Symᵘ→Sym
    : ⦃ Symᵘ A ⦄
    → Sym {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Symᵘ→Sym .sym = minv
  {-# INCOHERENT Symᵘ→Sym #-}
