{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Data.Vec where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Vec

open import Cubical.Instances.DecEq.Base

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

instance
  DecEqVec : ⦃ DecEq A ⦄ → DecEq (Vec A n)
  DecEq._≟_ DecEqVec = VecPath.discreteA→discreteVecA _≟_ _
