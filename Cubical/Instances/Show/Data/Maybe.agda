{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Maybe where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Maybe.Base

open import Cubical.Instances.Show.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  ShowMaybe : ⦃ Show A ⦄ → Show (Maybe A)
  Show.show ShowMaybe nothing  = "nothing"
  Show.show ShowMaybe (just x) = "just " ++ show x
