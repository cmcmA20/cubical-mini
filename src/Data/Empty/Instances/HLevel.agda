{-# OPTIONS --safe #-}
module Data.Empty.Instances.HLevel where

open import Foundations.Base

open import Meta.HLevel

open import Data.Empty.Base

instance
  HLevel-⊥ : {n : HLevel} → is-of-hlevel (suc n) ⊥
  HLevel-⊥ = is-prop→is-of-hlevel-suc ⊥-is-prop
