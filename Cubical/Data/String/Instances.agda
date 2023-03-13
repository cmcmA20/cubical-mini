{-# OPTIONS --safe #-}
module Cubical.Data.String.Instances where

open import Agda.Builtin.String using (primShowString)

open import Cubical.Foundations.Prelude

open import Cubical.Data.Char.Base

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

-- TODO
-- instance
--   DecEqString : DecEq String
--   DecEq._≟_ DecEqString = {!!}

-- instance
--   IsSetString : IsSet String
--   IsOfHLevel.iohl IsSetString = {!!}

instance
  ShowString : Show String
  Show.show ShowString = primShowString
