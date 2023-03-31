{-# OPTIONS --safe #-}
module Cubical.Instances.HLevels.Data.List where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.List

open import Cubical.Instances.HLevels.Base

private variable
  ℓ : Level
  A : Type ℓ
  h : HLevel

instance
  IsOfHLevelList : ⦃ IsOfHLevel (suc (suc h)) A ⦄ → IsOfHLevel (suc (suc h)) (List A)
  IsOfHLevel.iohl IsOfHLevelList = isOfHLevelList _ iohl
