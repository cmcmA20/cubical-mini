{-# OPTIONS --safe #-}
module Data.List.Membership where

open import Foundations.Base

open import Meta.Membership

open import Data.List.Base

private variable
  ℓ : Level
  A : Type ℓ
  x y : A
  xs : List A

data _∈ₗ_ {ℓ} {A : Type ℓ} (x : A) : List A → Type ℓ where
  here  : (p : x ＝ y) → x ∈ₗ (y ∷ xs)
  there : x ∈ₗ xs      → x ∈ₗ (y ∷ xs)

instance
  Membership-List : Membership A (List A) (level-of-type A)
  Membership-List ._∈_ = _∈ₗ_
