{-# OPTIONS --safe #-}
module Cubical.Interface.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels public
open import Cubical.Data.Nat.Base

private variable ℓ : Level

record @0 IsOfHLevel (@0 n : ℕ) (A : Type ℓ) : Type ℓ where
  field iohl : isOfHLevel n A

@0 IsContr : Type ℓ → Type ℓ
IsContr = IsOfHLevel 0

@0 IsProp : Type ℓ → Type ℓ
IsProp = IsOfHLevel 1

@0 IsSet : Type ℓ → Type ℓ
IsSet = IsOfHLevel 2
