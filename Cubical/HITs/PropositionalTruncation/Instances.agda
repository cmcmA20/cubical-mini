{-# OPTIONS --safe #-}
module Cubical.HITs.PropositionalTruncation.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  DecEqPropTrunc : DecEq ∥ A ∥₁
  DecEq._≟_ DecEqPropTrunc x y = yes (squash₁ x y)

instance
  IsPropPropTrunc : IsProp ∥ A ∥₁
  IsOfHLevel.iohl IsPropPropTrunc = squash₁

instance
  ShowPropTrunc : Show ∥ A ∥₁
  Show.show ShowPropTrunc _ = "∣?∣₁"
