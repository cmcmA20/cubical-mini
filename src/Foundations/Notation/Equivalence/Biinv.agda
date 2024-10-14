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

  record Biinv (x : A) (y : B) : 𝒰 (ℓf ⊔ ℓg ⊔ ℓfg ⊔ ℓgf) where
    no-eta-equality
    constructor make-biinv
    field
      to : F x y
      has-biinv : is-biinv to

    open has-retraction (has-biinv .fst)
      renaming (retraction to from; is-retraction to from-is-retraction)
      public
    open has-section (has-biinv .snd) public
{-# INLINE make-biinv #-}


open Biinv
module _
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄ where

  biinv
    : ∀ {x y} (f : F x y) (r : G y x) (rr : r retraction-of f)
      (s : G y x) (ss : s section-of f)
    → Biinv F G x y
  biinv f _ _ _ _ .to = f
  biinv f r rr s ss .has-biinv = make-is-biinv r rr s ss
  {-# INLINE biinv #-}

  ≅→≊ : ∀ {x y} → Iso F G x y → Biinv F G x y
  ≅→≊ i .to = i .Iso.to
  ≅→≊ i .has-biinv = qinv→is-biinv (≅→qinv i)
  {-# INLINE ≅→≊ #-}

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


open Biinv
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
    → Funlike ur (Biinv F G x y) ⌞ x ⌟ λ (e , a) → C (e .to , a)
  Funlike-≊ ._#_ e a = e .to # a

  Refl-≊
    : {ℓa ℓ : Level} {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ}
      ⦃ _ : Refl R ⦄ ⦃ _ : Trans R ⦄ ⦃ _ : HUnit-o R ⦄
    → Refl (Biinv R R)
  Refl-≊ .refl .to = refl
  Refl-≊ .refl .has-biinv = make-is-biinv refl (∙-id-o _) refl (∙-id-o _)
