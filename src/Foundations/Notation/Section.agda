{-# OPTIONS --safe #-}
module Foundations.Notation.Section where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Unital.Outer

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _
  {ℓa ℓb ℓb∙ ℓh : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {I : B → A → 𝒰 ℓh} {O : A → B → 𝒰 ℓh} {B∙ : B → B → 𝒰 ℓb∙}
  ⦃ _ : Refl B∙ ⦄ ⦃ _ : Comp I O B∙ ⦄ {x : A} {y : B} where

  _inner-inverse-of_ : (s : I y x) (r : O x y) → 𝒰 ℓb∙
  s inner-inverse-of r = s ∙ r ＝ refl

  _section-of_ = _inner-inverse-of_

  record has-section (r : O x y) : 𝒰 (ℓb∙ ⊔ ℓh) where
    no-eta-equality
    constructor make-section
    field
      section    : I y x
      is-section : section section-of r

open has-section public

-- aka split epimorphism
Retract
  : {ℓa ℓa∙ ℓb ℓh : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
    (F : B → A → 𝒰 ℓh) {G : A → B → 𝒰 ℓh} {A∙ : A → A → 𝒰 ℓa∙}
    ⦃ _ : Refl A∙ ⦄ ⦃ _ : Comp G F A∙ ⦄
    (x : A) (y : B) → 𝒰 (ℓa∙ ⊔ ℓh)
Retract F x y = Σ (F y x) has-section

module _
  {ℓa ℓb ℓh ℓa∙ : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  (I : A → B → 𝒰 ℓh) (O : B → A → 𝒰 ℓh) (A∙ : A → A → 𝒰 ℓa∙)
  ⦃ r : Refl A∙ ⦄ ⦃ s : Dual I O ⦄ ⦃ t : Comp I O A∙ ⦄ where

  record GInv-i : 𝒰 (ℓa ⊔ ℓa∙ ⊔ ℓb ⊔ ℓh) where
    no-eta-equality
    field ∙-inv-i : {x : A} {y : B} (p : I x y) → p section-of p ⁻¹

open GInv-i ⦃ ... ⦄ public

-- homogeneous correspondence having sections for all elements
HInv-i : (R : A → A → 𝒰 ℓ) ⦃ _ : Refl R ⦄ ⦃ _ : Sym R ⦄ ⦃ _ : Trans R ⦄ → Type _
HInv-i R = GInv-i R R R


-- binary operator having right inverses for all elements
record Inv-r
  {ℓ} (A : 𝒰 ℓ)
  ⦃ r : Pointed A ⦄ ⦃ s : Has-unary-op A ⦄ ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓ where
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

  Refl-Retract
    : ∀ {ℓa ℓ} {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ}
      ⦃ _ : Refl R ⦄ ⦃ _ : Trans R ⦄ ⦃ _ : HUnit-o R ⦄
    → Refl (Retract R)
  Refl-Retract .refl .fst = refl
  Refl-Retract .refl .snd .section = refl
  Refl-Retract .refl .snd .is-section = ∙-id-o _
