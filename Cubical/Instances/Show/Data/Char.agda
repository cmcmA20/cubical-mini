{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Char where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Char.Base

open import Cubical.Instances.Show.Base

instance
  ShowChar : Show Char
  Show.show ShowChar = primShowChar
