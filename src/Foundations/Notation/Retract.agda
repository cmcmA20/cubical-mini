{-# OPTIONS --safe #-}
module Foundations.Notation.Retract where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Transitivity

module _
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  {I : A → B → 𝒰 ℓ′} {O : B → A → 𝒰 ℓ} {I∙O : A → A → 𝒰 ℓ″}
  ⦃ r : Refl I∙O ⦄ ⦃ t : Trans I O I∙O ⦄ {x : A} {y : B} where

  _outer-inverse-of_ : (f : O y x) (g : I x y) → 𝒰 ℓ″
  f outer-inverse-of g = g ∙ f ＝ refl

  _retract-of_ = _outer-inverse-of_

  record has-retract (s : I x y) : 𝒰 (ℓ ⊔ ℓ″) where
    no-eta-equality
    constructor make-retract
    field
      retract    : O y x
      is-retract : retract retract-of s

open has-retract public
