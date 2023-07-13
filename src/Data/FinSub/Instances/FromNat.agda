{-# OPTIONS --safe #-}
module Data.FinSub.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Nat.Base
open import Data.Nat.Order.Computational

open import Data.Empty.Base
open import Data.FinSub.Base

instance
  Number-Fin : ∀ {n} → Number (Fin n)
  Number-Fin {n} .Number.Constraint m = m < n
  Number-Fin {n} .Number.fromNat m ⦃ (e) ⦄ = go m n e where
    go : ∀ k n → k < n → Fin n
    go zero zero p = absurd (¬sucn≤0 p)
    go zero (suc n) _ = fzero
    go (suc _) zero p = absurd (¬sucn≤0 p)
    go (suc k) (suc n) p = fsuc (go k n (≤-peel p))
