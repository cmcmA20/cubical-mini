{-# OPTIONS --safe #-}
module Cubical.Data.List.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base
open import Cubical.Data.List.Base
open import Cubical.Data.List.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show renaming (_++_ to _++ₛ_)

open DecEq ⦃ ... ⦄
open IsOfHLevel ⦃ ... ⦄
open Show ⦃ ... ⦄

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  DecEqList : ⦃ DecEq A ⦄ → DecEq (List A)
  DecEq._≟_ DecEqList = discreteList _≟_

instance
  IsOfHLevelList : ⦃ IsOfHLevel (suc (suc n))       A ⦄
                 →   IsOfHLevel (suc (suc n)) (List A)
  IsOfHLevel.iohl (IsOfHLevelList ⦃ Al ⦄) = isOfHLevelList _ (Al .iohl)

instance
  ShowList : ⦃ Show A ⦄ → Show (List A)
  Show.show ShowList xs = "[" ++ₛ ((foldr _++ₛ_ "" $ intersperse ", " $ map show xs) ++ₛ "]")
