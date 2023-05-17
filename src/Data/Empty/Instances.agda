{-# OPTIONS --safe #-}
module Data.Empty.Instances where

open import Foundations.Base
open import Foundations.HLevel
open import Meta.HLevel

open import Data.Empty.Base

private variable
  n : HLevel

instance
  H-Level-⊥ : H-Level (suc n) ⊥
  H-Level-⊥ = prop-instance ⊥-is-prop
