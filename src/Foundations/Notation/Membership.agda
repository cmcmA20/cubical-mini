{-# OPTIONS --safe #-}
module Foundations.Notation.Membership where

open import Foundations.Prim.Type
open import Foundations.Notation.Underlying

-- open import Data.Dec.Base
-- open import Data.Empty.Base

-- generalizing powerset membership
record Membership {ℓ ℓe} (A : Type ℓe) (ℙA : Type ℓ) ℓm : Type (ℓ ⊔ ℓsuc (ℓe ⊔ ℓm)) where
  infix 30 _∈_
  field _∈_ : A → ℙA → Type ℓm

open Membership ⦃ ... ⦄ public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  ℙA : Type ℓ′

infix 20 _⊆_
_⊆_ : ⦃ m : Membership A ℙA ℓ″ ⦄
    → ℙA → ℙA → Type (level-of-type A ⊔ ℓ″)
_⊆_ {A} S T = {a : A} → a ∈ S → a ∈ T

instance
  Membership-pow
    : ∀ {ℓ ℓ'} {A : Type ℓ} {P : Type ℓ'} ⦃ u : Underlying P ⦄
    → Membership A (A → P) _
  Membership-pow ._∈_ x S = ⌞ S x ⌟⁰
