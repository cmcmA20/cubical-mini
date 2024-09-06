{-# OPTIONS --safe #-}
module Foundations.Notation.Whiskering.Outer where

open import Foundations.Prim.Type

open import Foundations.Notation.Transitivity

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

module _
  {ℓᵃ ℓᵇ ℓᶜ ℓk ℓf ℓg ℓhf ℓhg ℓfg ℓo : Level}
  {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
  (K : B → C → 𝒰 ℓk)
  (F : A → B → 𝒰 ℓf) (F∙K : A → C → 𝒰 ℓhf) ⦃ _ : Trans F K F∙K ⦄
  (G : A → B → 𝒰 ℓg) (G∙K : A → C → 𝒰 ℓhg) ⦃ _ : Trans G K G∙K ⦄
  (FG : ∀ a b → F a b → G a b → 𝒰 ℓfg)
  (O : (a : A) (c : C) → F∙K a c → G∙K a c → 𝒰 ℓo) where

  record Whisker-o : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓf ⊔ ℓg ⊔ ℓfg ⊔ ℓk ⊔ ℓo) where
    no-eta-equality
    infixr 24 _▷_
    field
      _▷_ : {a : A} {b : B} {c : C} {f : F a b} {g : G a b}
          → FG a b f g → (k : K b c) → O a c (f ∙ k) (g ∙ k)

open Whisker-o ⦃ ... ⦄ public
