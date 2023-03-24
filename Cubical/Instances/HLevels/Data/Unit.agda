{-# OPTIONS --safe #-}
module Cubical.Instances.HLevels.Data.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Instances.HLevels.Base

private variable
  ℓ : Level

instance
  IsContrUnit : IsContr Unit
  IsOfHLevel.iohl IsContrUnit = isContrUnit

  IsContrUnit* : IsContr {ℓ} Unit*
  IsOfHLevel.iohl IsContrUnit* = isContrUnit*
