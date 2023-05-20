{-# OPTIONS --safe #-}
module Data.Bool.Instances.HLevel where

open import Foundations.Base
open import Meta.Reflection.HLevel

open import Data.Bool.Path

instance
  H-Level-Bool : ∀ {n} → H-Level (2 + n) Bool
  H-Level-Bool = basic-instance 2 Bool-is-set
