{-# OPTIONS --safe #-}
module Cubical.Data.Prod.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Prod.Base
open import Cubical.Data.Prod.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

open DecEq ⦃ ... ⦄
open IsOfHLevel ⦃ ... ⦄
open Show ⦃ ... ⦄

private variable
  ℓ ℓ′ : Level
  n : HLevel
  A : Type ℓ
  B : Type ℓ′

-- TODO
-- instance
--   DecEq× : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (A × B)
--   DecEq._≟_ DecEq× x y = {!!}

instance
  @0 IsOfHLevel× : ⦃ IsOfHLevel n A ⦄ → ⦃ IsOfHLevel n B ⦄
              → IsOfHLevel n (A × B)
  IsOfHLevel.iohl IsOfHLevel× = isOfHLevelProd _ iohl iohl

instance
  Show× : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A × B)
  Show.show Show× (a , b) = show a ++ (" , " ++ show b)
