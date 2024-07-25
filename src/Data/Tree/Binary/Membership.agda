{-# OPTIONS --safe #-}
module Data.Tree.Binary.Membership where

open import Foundations.Base

open import Data.Tree.Binary.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  tl tr : Tree A
  x y : A

data _∈ₜ_ {ℓ} {A : Type ℓ} (x : A) : Tree A → Type ℓ where
  here    : x ＝ y  → x ∈ₜ (leaf y)
  there-l : x ∈ₜ tl → x ∈ₜ (node tl tr)
  there-r : x ∈ₜ tr → x ∈ₜ (node tl tr)

instance
  Membership-Tree : Membership A (Tree A) (level-of-type A)
  Membership-Tree ._∈_ = _∈ₜ_
