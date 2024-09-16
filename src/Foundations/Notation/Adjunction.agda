{-# OPTIONS --safe #-}
module Foundations.Notation.Adjunction where

open import Foundations.Notation.Composition
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Underlying
open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Agda.Builtin.Sigma

-- Yeah, I know it's not on par with iso notation,
-- but doing it the same way proved to be intractable
module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓah ℓbh ℓf ℓg ℓiη ℓiε : Level}
  {A : 𝒰 ℓa} ⦃ ua : Underlying A ⦄
  {B : 𝒰 ℓb} ⦃ ub : Underlying B ⦄
  (A∙ : A → A → 𝒰 ℓa∙) ⦃ _ : Refl A∙ ⦄
  (B∙ : B → B → 𝒰 ℓb∙) ⦃ _ : Refl B∙ ⦄
  (F  : A → B → 𝒰 ℓf)  (G  : B → A → 𝒰 ℓg)
  ⦃ _ : Comp F G A∙ ⦄   ⦃ _ : Comp G F B∙ ⦄
  (C : A) (CHom : ⌞ C ⌟ → ⌞ C ⌟ → 𝒰 ℓah) ⦃ _ : Refl CHom ⦄ ⦃ _ : Trans CHom ⦄
  (D : B) (DHom : ⌞ D ⌟ → ⌞ D ⌟ → 𝒰 ℓbh) ⦃ _ : Refl DHom ⦄ ⦃ _ : Trans DHom ⦄
  (L : F C D)
  ⦃ _ : Funlike ur (F C D) ⌞ C ⌟ λ _ → ⌞ D ⌟ ⦄
  ⦃ _ : ∀ {x y} → Funlike ur (F C D) (CHom x y) λ (f , _) → DHom (f # x) (f # y) ⦄
  (R : G D C)
  ⦃ _ : Funlike ur (G D C) ⌞ D ⌟ λ _ → ⌞ C ⌟ ⦄
  ⦃ _ : ∀ {x y} → Funlike ur (G D C) (DHom x y) λ (f , _) → CHom (f # x) (f # y) ⦄
  (Iη : A∙ C C → A∙ C C → 𝒰 ℓiη)
  ⦃ _ : Funlike ur (Iη refl (L ∙ R)) ⌞ C ⌟ λ (_ , h) → CHom h (R # (L # h)) ⦄
  (Iε : B∙ D D → B∙ D D → 𝒰 ℓiε)
  ⦃ _ : Funlike ur (Iε (R ∙ L) refl) ⌞ D ⌟ λ (_ , f) → DHom (L # (R # f)) f ⦄
  where

  record Adjoint : 𝒰 (ua .ℓ-underlying ⊔ ub .ℓ-underlying ⊔ ℓah ⊔ ℓbh ⊔ ℓiη ⊔ ℓiε) where
    no-eta-equality
    constructor make-adjunction
    field
      η   : Iη refl    (L ∙ R)
      ε   : Iε (R ∙ L) refl
      zig : (x : ⌞ C ⌟) → Path (DHom (L # x) (L # x)) (L # (η # x) ∙ ε # (L # x)) refl
      zag : (y : ⌞ D ⌟) → Path (CHom (R # y) (R # y)) (η # (R # y) ∙ R # (ε # y)) refl

    adjunct-l : {x : ⌞ C ⌟} {y : ⌞ D ⌟} → DHom (L # x) y → CHom x (R # y)
    adjunct-l {x} p = η # x ∙ R # p

    adjunct-r : {x : ⌞ C ⌟} {y : ⌞ D ⌟} → CHom x (R # y) → DHom (L # x) y
    adjunct-r {y} p = L # p ∙ ε # y
  {-# INLINE make-adjunction #-}


record ⊣-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  infix 1 _⊣_
  field _⊣_ : A → B → R
open ⊣-notation ⦃ ... ⦄ public
