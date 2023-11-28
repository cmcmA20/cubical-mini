{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Nat.Base
open import Data.Nat.Order.Computational

open import Data.Empty.Base
open import Data.Fin.Computational.Base

instance
  Number-Fin : ∀ {n} → Number (Fin n)
  Number-Fin {n} .Number.Constraint m = m < n
  Number-Fin {n} .from-ℕ m ⦃ (e) ⦄ = go m n e where
    go : ∀ k n → k < n → Fin n
    go 0       (suc _) _ = fzero
    go (suc k) (suc n) p = fsuc (go k n (≤-peel {suc k} {n} p))
