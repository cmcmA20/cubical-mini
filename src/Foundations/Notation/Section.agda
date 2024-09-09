{-# OPTIONS --safe #-}
module Foundations.Notation.Section where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Notation.Reflexivity

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

module _
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  {I : B → A → 𝒰 ℓ′} {O : A → B → 𝒰 ℓ} {I∙O : B → B → 𝒰 ℓ″}
  ⦃ _ : Refl I∙O ⦄ ⦃ _ : Comp I O I∙O ⦄ {x : A} {y : B} where

  _inner-inverse-of_ : (s : I y x) (r : O x y) → 𝒰 ℓ″
  s inner-inverse-of r = s ∙ r ＝ refl

  _section-of_ = _inner-inverse-of_

  record has-section (r : O x y) : 𝒰 (ℓ′ ⊔ ℓ″) where
    no-eta-equality
    constructor make-section
    field
      section    : I y x
      is-section : section section-of r

open has-section public


module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) (I∙O : A → A → 𝒰 ℓ″)
  ⦃ r : Refl I∙O ⦄ ⦃ s : Dual I O ⦄ ⦃ t : Comp I O I∙O ⦄ where

  record GInv-i : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ″) where
    no-eta-equality
    field ∙-inv-i : {x : A} {y : B} (p : I x y) → p section-of p ⁻¹

open GInv-i ⦃ ... ⦄ public

-- homogeneous correspondence having sections for all elements
HInv-i : (R : A → A → 𝒰 ℓ) ⦃ _ : Refl R ⦄ ⦃ _ : Sym R ⦄ ⦃ _ : Trans R ⦄ → Type _
HInv-i R = GInv-i R R R


-- binary operator having right inverses for all elements
record Inv-r
  {ℓᵃ} (A : 𝒰 ℓᵃ)
  ⦃ r : Pointed A ⦄ ⦃ s : Has-unary-op A ⦄ ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓᵃ where
  no-eta-equality
  field <>-inv-r : (x : A) → x section-of (minv x)

open Inv-r ⦃ ... ⦄ public

instance
  Inv-r→HInv-i
    : ⦃ _ : Pointed A ⦄ ⦃ _ : Has-unary-op A ⦄
      ⦃ _ : Has-binary-op A ⦄ ⦃ _ : Inv-r A ⦄
    → HInv-i {A = ⊤} (λ _ _ → A)
  Inv-r→HInv-i .∙-inv-i = <>-inv-r
  {-# INCOHERENT Inv-r→HInv-i #-}
