{-# OPTIONS --safe #-}
module Data.Float.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat public

open import Data.Float.Base

instance
  From-ℕ-Float : From-ℕ Float
  From-ℕ-Float .From-ℕ.Constraint _ = ⊤
  From-ℕ-Float .from-ℕ n = ℕ→float n
