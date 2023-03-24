{-# OPTIONS --safe #-}
module Cubical.Data.Bool.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool.Base
open import Cubical.Data.Bool.Properties
open import Cubical.Data.FinSet.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.Finite
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

instance
  DecEqBool : DecEq Bool
  DecEq._≟_ DecEqBool false false = yes refl
  DecEq._≟_ DecEqBool false true  = no false≢true
  DecEq._≟_ DecEqBool true  false = no true≢false
  DecEq._≟_ DecEqBool true  true  = yes refl


instance
  FiniteBool : Finite Bool
  Finite.isFinite FiniteBool = isFinSetBool


instance
  IsSetBool : IsSet Bool
  IsOfHLevel.iohl IsSetBool = isSetBool


instance
  ShowBool : Show Bool
  Show.show ShowBool false = "false"
  Show.show ShowBool true  = "true"
