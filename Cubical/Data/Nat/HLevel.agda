{-# OPTIONS --safe #-}
module Cubical.Data.Nat.HLevel where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties

open import Cubical.Interface.HLevels

instance
  IsSetℕ : IsSet ℕ
  IsOfHLevel.iohl IsSetℕ = isSetℕ
