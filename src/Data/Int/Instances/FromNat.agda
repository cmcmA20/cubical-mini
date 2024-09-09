{-# OPTIONS --safe #-}
module Data.Int.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Int.Base
open import Data.Unit.Base

instance
  From-ℕ-ℤ : From-ℕ ℤ
  From-ℕ-ℤ .From-ℕ.Constraint _ = ⊤
  From-ℕ-ℤ .from-ℕ n = pos n
