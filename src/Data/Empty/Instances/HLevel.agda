{-# OPTIONS --safe #-}
module Data.Empty.Instances.HLevel where

open import Foundations.Base

open import Meta.HLevel

open import Data.Empty.Base

instance
  H-Level-⊥ : {n : HLevel} → H-Level (suc n) ⊥
  H-Level-⊥ = prop-instance ⊥-is-prop
