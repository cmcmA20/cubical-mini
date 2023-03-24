{-# OPTIONS --safe #-}
module Cubical.Instances.HLevels.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base

open import Cubical.Instances.HLevels.Base

private variable
  ℓ ℓ′ : Level
  h : HLevel
  A : Type ℓ
  B : A → Type ℓ′

instance
  IsPropIsOfHLevel : IsProp (IsOfHLevel h A)
  IsOfHLevel.iohl IsPropIsOfHLevel _ _ = IsOfHLevelExt (isPropIsOfHLevel _ _ _)

  IsOfHLevelSuc : ⦃ IsOfHLevel h A ⦄ → IsOfHLevel (suc h) A
  IsOfHLevel.iohl IsOfHLevelSuc = isOfHLevelSuc _ iohl

  -- should be true
  -- @0 IsOfHLevelLift : ⦃ Al : IsOfHLevel n A ⦄ → IsOfHLevel n (Lift {ℓ} {ℓ′} A)
  -- IsOfHLevel.iohl IsOfHLevelLift = {!!}

  -- IsPropErased : ⦃ Al : IsProp A ⦄ → IsProp (Erased A)
  -- IsOfHLevel.iohl (IsPropErased ⦃ Al ⦄) _ _ = []-cong [ Al .iohl _ _ ]
