{-# OPTIONS --safe #-}
module Data.Nat.Instances.Ord where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Ord

open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Nat.Base
open import Data.Nat.Order.Computational as ℕ-ord
open import Data.Nat.Path

<→≠ : ∀ {m n} → m ℕ-ord.< n → m ≠ n
<→≠ {0}     {0}     p _ = p
<→≠ {0}     {suc n} m<n = suc≠zero ∘ sym
<→≠ {suc m} {0}     sm<0 _ = sm<0
<→≠ {suc m} {suc n} sm<sn = <→≠ {m} {n} sm<sn ∘ ap pred

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
