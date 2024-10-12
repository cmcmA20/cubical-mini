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
  {ℓa ℓb ℓf ℓg ℓfg ℓgf : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  {F : A → B → 𝒰 ℓf} {G : B → A → 𝒰 ℓg}
  {F∙G : A → A → 𝒰 ℓfg} {G∙F : B → B → 𝒰 ℓgf}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
  {x : A} {y : B} where

  is-biinv : (f : F x y) → 𝒰 (ℓg ⊔ ℓfg ⊔ ℓgf)
  is-biinv f = Σ (has-retraction f)  λ _ → has-section f

  qinv→is-biinv : ∀ {f} → quasi-inverse f → is-biinv f
  qinv→is-biinv qi .fst .retraction = qi .quasi-inverse.inv
  qinv→is-biinv qi .fst .is-retraction =
    qi .quasi-inverse.inverses .Inverses.inv-i
  qinv→is-biinv qi .snd .section = qi .quasi-inverse.inv
  qinv→is-biinv qi .snd .is-section =
    qi .quasi-inverse.inverses .Inverses.inv-o
