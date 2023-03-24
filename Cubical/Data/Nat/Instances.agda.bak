{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Instances where

open import Agda.Builtin.String using (primShowNat)

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

instance
  DecEqℕ : DecEq ℕ
  DecEq._≟_ DecEqℕ = discreteℕ


instance
  IsSetℕ : IsSet ℕ
  IsOfHLevel.iohl IsSetℕ = isSetℕ


instance
  Showℕ : Show ℕ
  Show.show Showℕ = primShowNat
