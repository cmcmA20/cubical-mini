{-# OPTIONS --safe #-}
module Data.List.Membership where

open import Foundations.Base

open import Correspondences.Base
open import Correspondences.Unary.Decidable

import Data.List.Base as List
open List using (List)

open import Data.List.Correspondences.Unary.Any

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  x : A
  @0 xs : List A

_∈_ : A → @0 List A → Type _
x ∈ xs = Any (_＝ x) xs

_∉_ : A → @0 List A → Type _
x ∉ xs = ¬ (x ∈ xs)

_∈!_ : A → @0 List A → Type _
x ∈! xs = is-contr (x ∈ xs)

∈-ap : (f : A → B) → x ∈ xs → f x ∈ List.map f xs
∈-ap f = any-ap _ _ (ap f) _
