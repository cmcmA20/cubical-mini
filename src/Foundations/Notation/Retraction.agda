{-# OPTIONS --safe #-}
module Foundations.Notation.Retraction where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Notation.Reflexivity

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  {I : A → B → 𝒰 ℓ′} {O : B → A → 𝒰 ℓ} {I∙O : A → A → 𝒰 ℓ″}
  ⦃ r : Refl I∙O ⦄ ⦃ t : Comp I O I∙O ⦄ {x : A} {y : B} where

  _outer-inverse-of_ : (f : O y x) (g : I x y) → 𝒰 ℓ″
  f outer-inverse-of g = g ∙ f ＝ refl

  _retraction-of_ = _outer-inverse-of_

  record has-retraction (s : I x y) : 𝒰 (ℓ ⊔ ℓ″) where
    no-eta-equality
    constructor make-retract
    field
      retraction    : O y x
      is-retraction : retraction retraction-of s

open has-retraction public


module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) (I∙O : A → A → 𝒰 ℓ″) where

  record GInv-o ⦃ r : Refl I∙O ⦄ ⦃ s : Dual O I ⦄ ⦃ t : Comp I O I∙O ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ′ ⊔ ℓ″) where
    no-eta-equality
    field ∙-inv-o : {x : A} {y : B} (p : O y x) → p retraction-of p ⁻¹

open GInv-o ⦃ ... ⦄ public

-- homogeneous correspondence having retracts for all elements
HInv-o : (R : A → A → 𝒰 ℓ) ⦃ _ : Refl R ⦄ ⦃ _ : Sym R ⦄ ⦃ _ : Trans R ⦄ → Type _
HInv-o R = GInv-o R R R


-- binary operator having left inverses for all elements
record Inv-l
  {ℓᵃ} (A : 𝒰 ℓᵃ)
  ⦃ r : Pointed A ⦄ ⦃ s : Has-unary-op A ⦄ ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓᵃ where
  no-eta-equality
  field <>-inv-l : (x : A) → x retraction-of (minv x)

open Inv-l ⦃ ... ⦄ public

instance
  Inv-l→HInv-o
    : ⦃ _ : Pointed A ⦄ ⦃ _ : Has-unary-op A ⦄
      ⦃ _ : Has-binary-op A ⦄ ⦃ _ : Inv-l A ⦄
    → HInv-o {A = ⊤} (λ _ _ → A)
  Inv-l→HInv-o .∙-inv-o = <>-inv-l
  {-# INCOHERENT Inv-l→HInv-o #-}
