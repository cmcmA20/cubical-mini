{-# OPTIONS --safe #-}
module Cubical.HITs.PropositionalTruncation.HLevel where

open import Cubical.Foundations.Prelude

open import Cubical.Interface.HLevels

open import Cubical.HITs.PropositionalTruncation.Base

open IsOfHLevel ⦃ ... ⦄

private variable ℓ : Level

instance
  ∥∥₁HLevel : {P : Type ℓ} → IsOfHLevel 1 ∥ P ∥₁
  IsOfHLevel.iohl ∥∥₁HLevel = squash₁
