{-# OPTIONS --safe #-}
module Data.Nat.Instances.Number where

open import Foundations.Base
open import Meta.Literals

open import Data.Nat.Base

instance
  Number-ℕ : Number ℕ
  Number-ℕ .Number.Constraint _ = ⊤
  Number-ℕ .Number.fromNat n = n
