{-# OPTIONS --safe #-}
module Cubical.Data.Char.Instances where

open import Agda.Builtin.String using (primShowChar)

open import Cubical.Foundations.Prelude

open import Cubical.Data.Char.Base
open import Cubical.Data.Char.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.Finite
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

instance
  DecEqChar : DecEq Char
  DecEq._≟_ DecEqChar = discreteChar


-- -- nasty one!
-- instance
--   abstract
--     FiniteChar : Finite Char
--     Finite.isFinite FiniteChar = 1112064 , {!!}


instance
  @0 IsSetChar : IsSet Char
  IsOfHLevel.iohl IsSetChar = isSetChar


instance
  ShowChar : Show Char
  Show.show ShowChar = primShowChar
