{-# OPTIONS --safe #-}
module Data.Nat.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Nat.Base
open import Data.String.Base

instance
  Show-ℕ : Show ℕ
  Show-ℕ = default-show show-ℕ
