{-# OPTIONS --safe #-}
module Foundations.Notation.Whiskering.Inner where

open import Foundations.Prim.Type

open import Foundations.Notation.Composition

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

module _
  {ℓᵃ ℓᵇ ℓᶜ ℓh ℓf ℓg ℓhf ℓhg ℓfg ℓo : Level}
  {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
  (H : A → B → 𝒰 ℓh)
  (F : B → C → 𝒰 ℓf) (H∙F : A → C → 𝒰 ℓhf) ⦃ _ : Comp H F H∙F ⦄
  (G : B → C → 𝒰 ℓg) (H∙G : A → C → 𝒰 ℓhg) ⦃ _ : Comp H G H∙G ⦄
  (FG : ∀ b c → F b c → G b c → 𝒰 ℓfg)
  (O : (a : A) (c : C) → H∙F a c → H∙G a c → 𝒰 ℓo) where

  record Whisker-i : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓf ⊔ ℓg ⊔ ℓfg ⊔ ℓh ⊔ ℓo) where
    no-eta-equality
    infixr 24 _◁_
    field
      _◁_ : {a : A} {b : B} {c : C} {f : F b c} {g : G b c}
          → (h : H a b) → FG b c f g → O a c (h ∙ f) (h ∙ g)

open Whisker-i ⦃ ... ⦄ public
