{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Data.List where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List

open import Cubical.Instances.DecEq.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  DecEqList : ⦃ DecEq A ⦄ → DecEq (List A)
  DecEq._≟_ DecEqList = discreteList _≟_
