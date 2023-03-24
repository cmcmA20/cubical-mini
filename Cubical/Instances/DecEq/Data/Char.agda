{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Data.Char where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Char

open import Cubical.Instances.DecEq.Base

instance
  DecEqChar : DecEq Char
  DecEq._≟_ DecEqChar = discreteChar
