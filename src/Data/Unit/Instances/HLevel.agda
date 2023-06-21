{-# OPTIONS --safe #-}
module Data.Unit.Instances.HLevel where

open import Foundations.Base

open import Meta.HLevel

open import Data.Unit.Path

instance
  H-Level-⊤ : ∀ {n} → is-of-hlevel n ⊤
  H-Level-⊤ = is-of-hlevel-+-left 0 _ ⊤-is-contr
