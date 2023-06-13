{-# OPTIONS --safe #-}
module Data.Unit.Instances.HLevel where

open import Foundations.Base

open import Meta.HLevel

open import Data.Unit.Path

instance
  H-Level-⊤ : ∀ {n} → H-Level n ⊤
  H-Level-⊤ = basic-instance 0 ⊤-is-contr
