{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Instances.Map where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Map
open import Meta.Inductive

open import Data.Truncation.Propositional.Base

instance
  Map-∥-∥₁ : Map (eff ∥_∥₁)
  Map-∥-∥₁ .map f = rec! (∣_∣₁ ∘ f) where
    instance _ = hlevel-prop-instance squash₁
