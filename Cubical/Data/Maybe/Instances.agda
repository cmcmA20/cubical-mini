{-# OPTIONS --safe #-}
module Cubical.Data.Maybe.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Maybe.Base
open import Cubical.Data.Maybe.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

open DecEq ⦃ ... ⦄
open IsOfHLevel ⦃ ... ⦄
open Show ⦃ ... ⦄

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  DecEqMaybe : ⦃ DecEq A ⦄ → DecEq (Maybe A)
  DecEq._≟_ DecEqMaybe = discreteMaybe _≟_

instance
  IsOfHLevelMaybe : ⦃ IsOfHLevel (suc (suc n)) A ⦄
                  → IsOfHLevel (suc (suc n)) (Maybe A)
  IsOfHLevel.iohl (IsOfHLevelMaybe ⦃ Al ⦄) = isOfHLevelMaybe _ (Al .iohl)

instance
  ShowMaybe : ⦃ Show A ⦄ → Show (Maybe A)
  Show.show ShowMaybe nothing  = "nothing"
  Show.show ShowMaybe (just x) = "just " ++ show x
