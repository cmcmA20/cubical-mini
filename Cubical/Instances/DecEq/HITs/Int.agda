{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.HITs.Int where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.Int

open import Cubical.Instances.DecEq.Base

instance
  DecEqℤ : DecEq ℤ
  DecEq._≟_ DecEqℤ = discreteℤ
