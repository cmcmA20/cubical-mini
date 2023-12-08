{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Map

open import Data.Vec.Inductive.Base as Vec

instance
  Map-Vec : ∀ {@0 n} → Map (eff (λ T → Vec T n))
  Map-Vec .Map.map = Vec.map
