{-# OPTIONS --safe #-}
module Cubical.Data.Char.Instances where

open import Agda.Builtin.String using (primShowChar)

open import Cubical.Foundations.Prelude

open import Cubical.Data.Char.Base

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

-- TODO
-- instance
--   DecEqChar : DecEq Char
--   DecEq._≟_ DecEqChar = {!!}

-- instance
--   IsSetChar : IsSet Char
--   IsOfHLevel.iohl IsSetChar = {!!}

instance
  ShowChar : Show Char
  Show.show ShowChar = primShowChar
