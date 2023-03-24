{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Prod where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Prod.Base

open import Cubical.Instances.Show.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

instance
  Show× : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A × B)
  Show.show Show× (a , b) = show a ++ (" , " ++ show b)
