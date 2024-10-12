{-# OPTIONS --safe #-}
module Foundations.Notation.Equivalence.Biinv where

open import Foundations.Prim.Type

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Notation.Invertibility.Bi
open import Foundations.Notation.Invertibility.Quasi
open import Foundations.Notation.Isomorphism
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Retraction
open import Foundations.Notation.Section
open import Foundations.Notation.Underlying
open import Foundations.Notation.Unital.Outer

open import Agda.Builtin.Sigma

module _
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  (F : A → B → 𝒰 ℓf) (G : B → A → 𝒰 ℓg)
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄ where

  Biinv : (x : A) (y : B) → 𝒰 (ℓf ⊔ ℓg ⊔ ℓfg ⊔ ℓgf)
  Biinv x y = Σ (F x y) is-biinv


module _
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄ where
  open Iso

  ≅→≊ : ∀ {x y} → Iso F G x y → Biinv F G x y
  ≅→≊ i .fst = i .to
  ≅→≊ i .snd = qinv→is-biinv (≅→qinv i)

HBiinv
  : ∀ {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) ⦃ _ : Refl R ⦄ ⦃ _ : Trans R ⦄
  → (x y : A) → 𝒰 ℓ
HBiinv R = Biinv R R


record ≊-notation {ℓa ℓb ℓ}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰ω where
  infix 1 _≊_
  field _≊_ : A → B → R
open ≊-notation ⦃ ... ⦄ public
{-# DISPLAY ≊-notation._≊_ _ a b = a ≊ b #-}


instance
  Funlike-≊
    : {ℓa ℓb ℓc ℓf ℓg ℓfg ℓgf : Level}
      {A : 𝒰 ℓa} {B : 𝒰 ℓb} ⦃ ua : Underlying A ⦄
      {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
      {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
      {x : A} {y : B} {C : Σ (F x y) (λ _ → ⌞ x ⌟) → 𝒰 ℓc}
      ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
      ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
      ⦃ f : Funlike ur (F x y) ⌞ x ⌟ C ⦄
    → Funlike ur (Biinv F G x y) ⌞ x ⌟ λ (i , a) → C (i .fst , a)
  Funlike-≊ ._#_ i a = i .fst # a

  Refl-≊
    : {ℓa ℓ : Level} {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ}
      ⦃ _ : Refl R ⦄ ⦃ _ : Trans R ⦄ ⦃ _ : HUnit-o R ⦄
    → Refl (Biinv R R)
  Refl-≊ .refl .fst = refl
  Refl-≊ .refl .snd .fst .retraction = refl
  Refl-≊ .refl .snd .fst .is-retraction = ∙-id-o _
  Refl-≊ .refl .snd .snd .section = refl
  Refl-≊ .refl .snd .snd .is-section = ∙-id-o _
