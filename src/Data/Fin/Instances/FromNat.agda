{-# OPTIONS --safe #-}
module Data.Fin.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Nat.Base
open import Data.Nat.Order.Inductive

open import Data.Fin.Base

instance
  From-ℕ-Fin : ∀ {n} → From-ℕ (Fin n)
  From-ℕ-Fin {n} .From-ℕ.Constraint m = m < n
  From-ℕ-Fin {n} .from-ℕ m ⦃ (e) ⦄ = go m n e where
    go : ∀ k n → k < n → Fin n
    go zero    (suc _) _       = fzero
    go (suc k) (suc n) (s≤s e) = fsuc (go k n e)
