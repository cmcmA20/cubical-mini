{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.String where

open import Cubical.Foundations.Prelude

open import Cubical.Data.String.Base

open import Cubical.Instances.Show.Base

instance
  ShowString : Show String
  Show.show ShowString = showStr
