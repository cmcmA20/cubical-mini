{-# OPTIONS --safe #-}
module Data.Nat.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Nat.Base
open import Data.Unit.Base

instance
  From-ℕ-ℕ : From-ℕ ℕ
  From-ℕ-ℕ .From-ℕ.Constraint _ = ⊤
  From-ℕ-ℕ .from-ℕ n = n
