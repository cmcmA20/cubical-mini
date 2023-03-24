{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Data.Maybe where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Maybe

open import Cubical.Instances.DecEq.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  DecEqMaybe : ⦃ DecEq A ⦄ → DecEq (Maybe A)
  DecEq._≟_ DecEqMaybe = discreteMaybe _≟_
