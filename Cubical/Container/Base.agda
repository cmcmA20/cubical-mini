{-# OPTIONS --safe #-}
module Cubical.Container.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

infix 5 _▶_
record Container (ℓˢ ℓᵖ : Level) : Type (ℓ-suc (ℓ-max ℓˢ ℓᵖ)) where
  constructor _▶_
  field
    Shape    : Type ℓˢ
    Position : Shape → Type ℓᵖ
open Container public

private variable
  ℓ ℓˢ ℓᵖ : Level

⟦_⟧ : Container ℓˢ ℓᵖ → Type ℓ → Type (ℓ-max ℓ (ℓ-max ℓˢ ℓᵖ))
⟦ S ▶ P ⟧ X = Σ[ s ∈ S ] (P s → X)

_∈_ : {X : Type ℓ} {S : Type ℓˢ} {P : S → Type ℓᵖ}
    → X → ⟦ S ▶ P ⟧ X → Type (ℓ-max ℓ ℓᵖ)
x ∈ xs = fiber (xs .snd) x

_∈!_ : {X : Type ℓ} {S : Type ℓˢ} {P : S → Type ℓᵖ}
     → X → ⟦ S ▶ P ⟧ X → Type (ℓ-max ℓ ℓᵖ)
x ∈! xs = isContr (x ∈ xs)
