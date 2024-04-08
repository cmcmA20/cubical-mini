{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat public

open import Data.Nat.Order.Inductive
  using ()
  renaming (_<_ to <-from-nat-constraint)
  public
open import Data.Nat.Order.Inductive

open import Data.Fin.Inductive.Base

instance
  From-ℕ-Fin : ∀ {n} → From-ℕ (Fin n)
  From-ℕ-Fin {n} .From-ℕ.Constraint m = m < n
  From-ℕ-Fin {n} .from-ℕ m ⦃ (e) ⦄ = go m n e where
    go : ∀ k n → k < n → Fin n
    go zero    (suc n) _       = fzero
    go (suc k) (suc n) (s≤s e) = fsuc (go k n e)
