{-# OPTIONS --safe #-}
module Meta.Membership where

open import Foundations.Base

open import Meta.Underlying

open import Data.Dec.Base
open import Data.Empty.Base

-- generalizing powerset membership
record Membership {ℓ ℓe} (A : Type ℓe) (ℙA : Type ℓ) ℓm : Type (ℓ ⊔ ℓsuc (ℓe ⊔ ℓm)) where
  infix 30 _∈_
  field _∈_ : A → ℙA → Type ℓm

open Membership ⦃ ... ⦄ public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  ℙA : Type ℓ′

infix 30 _∉_
_∉_ : ⦃ m : Membership A ℙA ℓ″ ⦄ → A → ℙA → Type ℓ″
x ∉ y = ¬ x ∈ y

infix 20 _⊆_
_⊆_ : ⦃ m : Membership A ℙA ℓ″ ⦄
    → ℙA → ℙA → Type (level-of-type A ⊔ ℓ″)
_⊆_ {A} S T = {a : A} → a ∈ S → a ∈ T

infix 30 _∈!_ _∉!_ _∈?_ _∈!?_
_∈!_ _∉!_ : ⦃ m : Membership A ℙA ℓ″ ⦄ → A → ℙA → Type ℓ″
x ∈! y = is-contr (x ∈ y)
x ∉! y = ¬ x ∈! y

_∈?_
  : ⦃ m : Membership A ℙA ℓ″ ⦄
  → ⦃ d : {y : A} {ys : ℙA} → Dec (y ∈ ys) ⦄
  → (x : A) (xs : ℙA) → Dec (x ∈ xs)
_∈?_ = _~?_

_∈!?_
  : ⦃ m : Membership A ℙA ℓ″ ⦄
  → ⦃ d : {y : A} {ys : ℙA} → Dec (y ∈! ys) ⦄
  → (x : A) (xs : ℙA) → Dec (x ∈! xs)
_∈!?_ = _~?_

instance
  Membership-pow
    : ∀ {ℓ ℓ'} {A : Type ℓ} {P : Type ℓ'} ⦃ u : Underlying P ⦄
    → Membership A (A → P) _
  Membership-pow ._∈_ x S = ⌞ S x ⌟⁰
