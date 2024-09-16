{-# OPTIONS --safe #-}
module Foundations.Notation.Duality where

open import Foundations.Prim.Type
open import Agda.Builtin.Unit

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : 𝒰 ℓᵃ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) where

  Duality : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′)
  Duality = {x : A} {y : B} → I x y → O y x

  record Dual : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′) where
    no-eta-equality
    infixl 60 _ᵒᵖ
    field _ᵒᵖ : Duality

    -- TODO split this out?
    -- TODO additive notation
    infix 90 _⁻¹
    _⁻¹ = _ᵒᵖ

open Dual ⦃ ... ⦄ public


-- homogeneous duality is symmetry
Sym : (A → A → 𝒰 ℓ) → 𝒰 _
Sym R = Dual R R

sym : {ℓᵃ ℓ : Level} {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ} ⦃ r : Sym R ⦄
    → {x y : A} → R x y → R y x
sym = _ᵒᵖ


-- unindexed duality is having a chosen automorphism
record Has-unary-op {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field minv : A → A
open Has-unary-op ⦃ ... ⦄ public


instance
  Has-unary-op→Sym
    : ⦃ Has-unary-op A ⦄
    → Sym {A = ⊤} (λ _ _ → A)
  Has-unary-op→Sym ._ᵒᵖ = minv
  {-# INCOHERENT Has-unary-op→Sym #-}
