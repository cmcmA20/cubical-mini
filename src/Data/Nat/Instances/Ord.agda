{-# OPTIONS --safe #-}
module Data.Nat.Instances.Ord where

open import Foundations.Prelude

open import Meta.Ord

open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Dec.Tri.Base
open import Data.Nat.Base
open import Data.Nat.Order.Inductive as ℕ-ord
open import Data.Nat.Path

instance
  Ord-ℕ : Ord ℕ
  Ord-ℕ .Ord.ℓo = 0ℓ
  Ord-ℕ .Ord._<_ = ℕ-ord._<_
  Ord-ℕ .Ord.<-thin = hlevel 1
  Ord-ℕ .Ord.<-trans {x} {y} {z} = <-trans {x} {y} {z}
  Ord-ℕ .Ord._≤?_ x y with ≤-split x y
  ... | inl x<y = lt x<y (<→≠ x<y) (<-asym {x} x<y)
  ... | inr (inl y<x) = gt (<-asym {y} y<x) (<→≠ y<x ∘ sym) y<x
  ... | inr (inr x=y) = eq
    (λ x<y → <-irr {x} (subst (x ℕ-ord.<_) (sym x=y) x<y))
    x=y
    (λ y<x → <-irr {y} (subst (y ℕ-ord.<_) x=y y<x))
  {-# OVERLAPPING Ord-ℕ #-}
