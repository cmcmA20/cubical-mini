{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.String.Base

open import Cubical.Instances.Show.Base

instance
  Showℕ : Show ℕ
  Show.show Showℕ = showNat
