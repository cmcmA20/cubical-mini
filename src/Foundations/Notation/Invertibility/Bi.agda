{-# OPTIONS --safe #-}
module Foundations.Notation.Invertibility.Bi where

open import Foundations.Prim.Type

open import Foundations.Notation.Invertibility.Quasi
open import Foundations.Notation.Composition
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Retraction
open import Foundations.Notation.Section

open import Agda.Builtin.Sigma

module _
  {ℓa ℓa∙ ℓb ℓb∙ ℓh : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {A∙ : A → A → 𝒰 ℓa∙} {B∙ : B → B → 𝒰 ℓb∙}
  {F : A → B → 𝒰 ℓh} {G : B → A → 𝒰 ℓh}
  ⦃ _ : Refl A∙ ⦄ ⦃ _ : Comp F G A∙ ⦄
  ⦃ _ : Refl B∙ ⦄ ⦃ _ : Comp G F B∙ ⦄
  {x : A} {y : B} where

  is-biinv : (f : F x y) → 𝒰 (ℓa∙ ⊔ ℓb∙ ⊔ ℓh)
  is-biinv f = Σ (has-retraction f)  λ _ → has-section f

  make-is-biinv
    : ∀ {f} (r : G y x) (rr : r retraction-of f)
      (s : G y x) (ss : s section-of f)
    → is-biinv f
  make-is-biinv r rr s ss .fst = make-retraction r rr
  make-is-biinv r rr s ss .snd = make-section s ss
  {-# INLINE make-is-biinv #-}

  qinv→is-biinv : ∀ {f} → quasi-inverse f → is-biinv f
  qinv→is-biinv qi .fst .retraction = qi .quasi-inverse.inv
  qinv→is-biinv qi .fst .is-retraction =
    qi .quasi-inverse.inverses .Inverses.inv-i
  qinv→is-biinv qi .snd .section = qi .quasi-inverse.inv
  qinv→is-biinv qi .snd .is-section =
    qi .quasi-inverse.inverses .Inverses.inv-o
  {-# INLINE qinv→is-biinv #-}
