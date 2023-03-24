{-# OPTIONS --safe --overlapping-instances --instance-search-depth=1 #-}
module Cubical.Instances.HLevels.Data.Path where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base

open import Cubical.Instances.HLevels.Base
open import Cubical.Instances.HLevels.Properties

private variable
  ℓ ℓ′ : Level
  h : HLevel
  A : Type ℓ
  B : A → Type ℓ′

instance
  IsOfHLevelPath : ⦃ IsOfHLevel (suc h) A ⦄ → {x y : A} → IsOfHLevel h (x ≡ y)
  IsOfHLevel.iohl IsOfHLevelPath = isOfHLevelPath' _ iohl _ _

  IsProp→isContrPath : ⦃ IsProp A ⦄ → {x y : A} → IsContr (x ≡ y)
  IsOfHLevel.iohl IsProp→isContrPath = iohl _ _ , isProp→isSet iohl _ _ _
