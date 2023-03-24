{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Data.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat

open import Cubical.Instances.DecEq.Base

instance
  DecEqℕ : DecEq ℕ
  DecEq._≟_ DecEqℕ = discreteℕ
