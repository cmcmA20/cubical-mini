{-# OPTIONS --safe #-}
module Data.Fin.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Nat.Base
open import Data.Nat.Order.Inductive

open import Data.Fin.Base

instance
  Number-Fin : ∀ {n} → Number (Fin n)
  Number-Fin {n} .Number.Constraint m = m < n
  Number-Fin {n} .from-ℕ m ⦃ (e) ⦄ = go m n e where
    go : ∀ k n → k < n → Fin n
    go zero    (suc _) _       = fzero
    go (suc k) (suc n) (s≤s e) = fsuc (go k n e)
