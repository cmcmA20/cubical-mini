{-# OPTIONS --safe #-}
module Data.Float.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Float.Base
open import Data.Unit.Base

instance
  From-ℕ-Float : From-ℕ Float
  From-ℕ-Float .From-ℕ.Constraint _ = ⊤
  From-ℕ-Float .from-ℕ n = ℕ→float n
