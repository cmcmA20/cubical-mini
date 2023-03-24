{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit.Base

open import Cubical.Instances.Show.Base

private variable
  ℓ : Level

instance
  ShowUnit : Show Unit
  Show.show ShowUnit tt = "tt"

  ShowUnit* : Show {ℓ} Unit*
  Show.show ShowUnit* (lift tt) = "tt"
