{-# OPTIONS --safe #-}
module Cubical.Instances.Show.HITs.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base

open import Cubical.HITs.Int.Base

open import Cubical.Instances.Show.Base
open import Cubical.Instances.Show.Data.Nat

instance
  Showℤ : Show ℤ
  Show.show Showℤ (neg 0)       = "0"
  Show.show Showℤ (neg (suc n)) = "-" ++ show n
  Show.show Showℤ (pos 0)       = "0"
  Show.show Showℤ (pos (suc n)) = show n
  Show.show Showℤ (0₋≡0₊ _) = "0"
