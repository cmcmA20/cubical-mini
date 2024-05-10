{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Empty.Base
open import Data.Fin.Computational.Base
open import Data.Nat.Base
open import Data.Nat.Order.Inductive.Base

instance
  From-ℕ-Fin : ∀ {n} → From-ℕ (Fin n)
  From-ℕ-Fin {n} .From-ℕ.Constraint m = m < n
  From-ℕ-Fin {n} .from-ℕ m ⦃ (e) ⦄ = go m n e where
    go : ∀ k n → k < n → Fin n
    go 0       (suc _) _ = fzero
    go (suc k) (suc n) p = fsuc (go k n (≤-peel {suc k} {n} p))
