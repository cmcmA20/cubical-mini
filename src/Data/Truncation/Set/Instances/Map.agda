{-# OPTIONS --safe #-}
module Data.Truncation.Set.Instances.Map where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Inductive

open import Data.Truncation.Set.Base

instance
  Map-∥-∥₂ : Map (eff ∥_∥₂)
  Map-∥-∥₂ .map f = rec! (∣_∣₂ ∘ f) where
    instance _ = hlevel-basic-instance 2 squash₂
