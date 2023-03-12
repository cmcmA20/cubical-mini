{-# OPTIONS --safe #-}
module Cubical.Data.List.HLevel where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.List.Base
open import Cubical.Data.List.Properties

open import Cubical.Interface.HLevels

open IsOfHLevel ⦃ ... ⦄

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  IsOfHLevelList : ⦃ Al : IsOfHLevel (suc (suc n)) A ⦄
                 → IsOfHLevel (suc (suc n)) (List A)
  IsOfHLevel.iohl (IsOfHLevelList ⦃ Al ⦄) = isOfHLevelList _ (Al .iohl)
