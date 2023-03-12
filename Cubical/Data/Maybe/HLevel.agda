{-# OPTIONS --safe #-}
module Cubical.Data.Maybe.HLevel where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Maybe.Base
open import Cubical.Data.Maybe.Properties

open import Cubical.Interface.HLevels

open IsOfHLevel ⦃ ... ⦄

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  IsOfHLevelMaybe : ⦃ IsOfHLevel (suc (suc n)) A ⦄
                  → IsOfHLevel (suc (suc n)) (Maybe A)
  IsOfHLevel.iohl (IsOfHLevelMaybe ⦃ Al ⦄) = isOfHLevelMaybe _ (Al .iohl)
