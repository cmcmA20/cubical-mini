{-# OPTIONS --safe #-}
module Cubical.Data.Unit.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinSet.Properties
open import Cubical.Data.Unit.Base
open import Cubical.Data.Unit.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.Finite
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

private variable
  ℓ : Level

instance
  DecEqUnit : DecEq Unit
  DecEq._≟_ DecEqUnit tt tt = yes refl

  DecEqUnit* : DecEq {ℓ} Unit*
  DecEq._≟_ DecEqUnit* (lift tt) (lift tt) = yes refl


instance
  FiniteUnit : Finite Unit
  Finite.isFinite FiniteUnit = isFinSetUnit


instance
  ShowUnit : Show Unit
  Show.show ShowUnit tt = "tt"

  ShowUnit* : Show {ℓ} Unit*
  Show.show ShowUnit* (lift tt) = "tt"


instance
  IsContrUnit : IsContr Unit
  IsOfHLevel.iohl IsContrUnit = isContrUnit

  IsContrUnit* : IsContr {ℓ} Unit*
  IsOfHLevel.iohl IsContrUnit* = isContrUnit*
