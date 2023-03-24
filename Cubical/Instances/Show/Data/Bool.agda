{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Bool where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool.Base

open import Cubical.Instances.Show.Base

instance
  ShowBool : Show Bool
  Show.show ShowBool false = "false"
  Show.show ShowBool true  = "true"
