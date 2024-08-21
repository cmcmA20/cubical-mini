{-# OPTIONS --safe #-}
module Foundations.Notation.Membership where

open import Foundations.Notation.Logic
open import Foundations.Notation.Underlying
open import Foundations.Prim.Type
open import Foundations.Pi.Base
open import Foundations.Sigma.Base

-- generalizing powerset membership
record Membership {ℓ ℓe} (A : Type ℓe) (ℙA : Type ℓ) ℓm : Type (ℓ ⊔ ℓsuc (ℓe ⊔ ℓm)) where
  infix 30 _∈_
  field _∈_ : A → ℙA → Type ℓm
open Membership ⦃ ... ⦄ public

private variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ : Level
  A : Type ℓ
  ℙA₁ : Type ℓ′
  ℙA₂ : Type ℓ″

infix 20 _⊆_ _≬_
_⊆_ _≬_
  : ⦃ m₁ : Membership A ℙA₁ ℓ‴ ⦄ ⦃ m₂ : Membership A ℙA₂ ℓ⁗ ⦄
  → ℙA₁ → ℙA₂ → Type (level-of-type A ⊔ ℓ‴ ⊔ ℓ⁗)
_⊆_ {A} S T = ∀[ a ꞉ A ] (a ∈ S ⇒ a ∈ T)
_≬_ {A} S T = Σ[ a ꞉ A ] (a ∈ S × a ∈ T)


record Intersection {ℓ ℓ′ ℓ″} (A : Type ℓ) (B : Type ℓ′) (R : Type ℓ″) : Typeω where
  infixr 22 _∩_
  field _∩_ : A → B → R
open Intersection ⦃ ... ⦄ public

record Union {ℓ ℓ′ ℓ″} (A : Type ℓ) (B : Type ℓ′) (R : Type ℓ″) : Typeω where
  infixr 21 _∪_
  field _∪_ : A → B → R
open Union ⦃ ... ⦄ public


instance
  Membership-pow
    : {A : Type ℓ} {P : Type ℓ′} ⦃ u : Underlying P ⦄
    → Membership A (A → P) (u .ℓ-underlying)
  Membership-pow ._∈_ x S = ⌞ S x ⌟
  {-# OVERLAPPABLE Membership-pow #-}

  Intersection-pow
    : {A : Type ℓ} {B : Type ℓ′} ⦃ ua : Underlying A ⦄ ⦃ ub : Underlying B ⦄
      {P : Type ℓ″} {X : Type ℓ‴}
      ⦃ _ : ×-notation (Type (ua .ℓ-underlying)) (Type (ub .ℓ-underlying)) P ⦄
    → Intersection (X → A) (X → B) (X → P)
  Intersection-pow ._∩_ S T x = ⌞ S x ⌟ × ⌞ T x ⌟
  {-# OVERLAPPABLE Intersection-pow #-}
