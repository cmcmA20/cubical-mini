{-# OPTIONS --safe #-}
module Foundations.Notation.Duality where

open import Foundations.Prim.Type
open import Agda.Builtin.Unit

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _
  {ℓa ℓb ℓh : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  (I : A → B → 𝒰 ℓh) (O : B → A → 𝒰 ℓh) where

  Duality : {x : A} {y : B} (i : I x y) → 𝒰 ℓh
  Duality {x} {y} i = O y x

  record Dual : 𝒰 (ℓa ⊔ ℓb ⊔ ℓh) where
    no-eta-equality
    infixl 60 _ᵒᵖ
    field _ᵒᵖ : {x : A} {y : B} (i : I x y) → Duality i

    -- TODO split this out?
    -- TODO additive notation
    infix 90 _⁻¹
    _⁻¹ = _ᵒᵖ

open Dual ⦃ ... ⦄ public
{-# DISPLAY Dual._ᵒᵖ _ a = a ᵒᵖ #-}
{-# DISPLAY Dual._⁻¹ _ a = a ⁻¹ #-}


-- homogeneous duality is symmetry
Sym : (A → A → 𝒰 ℓ) → 𝒰 _
Sym R = Dual R R

sym : {ℓᵃ ℓ : Level} {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ} ⦃ r : Sym R ⦄
    → {x y : A} → R x y → R y x
sym = _ᵒᵖ


-- unindexed duality is having a chosen automorphism
record Has-unary-op {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field minv : A → A
open Has-unary-op ⦃ ... ⦄ public
{-# DISPLAY Has-unary-op.minv _ a = minv a #-}


instance
  Has-unary-op→Sym
    : ⦃ Has-unary-op A ⦄
    → Sym {A = ⊤} (λ _ _ → A)
  Has-unary-op→Sym ._ᵒᵖ = minv
  {-# INCOHERENT Has-unary-op→Sym #-}
