{-# OPTIONS --safe --overlapping-instances --instance-search-depth=1 #-}
module Cubical.Instances.HLevels.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Erased

open import Cubical.Data.Nat.Base

open import Cubical.Truncation.Propositional.Base
open import Cubical.Truncation.Set.Base

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

  IsPropErased : ⦃ IsProp A ⦄ → IsProp (Erased A)
  IsOfHLevel.iohl IsPropErased _ _ = []-cong [ iohl _ _ ]

  IsPropTruncation : IsProp ∥ A ∥₁
  IsOfHLevel.iohl IsPropTruncation = squash₁

  IsSetTruncation : IsSet ∥ A ∥₂
  IsOfHLevel.iohl IsSetTruncation = squash₂
