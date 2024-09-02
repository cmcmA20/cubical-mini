{-# OPTIONS --safe #-}
module Foundations.Notation.Section where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Transitivity

module _
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  {I : B → A → 𝒰 ℓ′} {O : A → B → 𝒰 ℓ} {I∙O : B → B → 𝒰 ℓ″}
  ⦃ _ : Refl I∙O ⦄ ⦃ _ : Trans I O I∙O ⦄ {x : A} {y : B} where

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
