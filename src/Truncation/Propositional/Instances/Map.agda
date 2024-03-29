{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.Map where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Map

open import Truncation.Propositional.Base

instance
  Map-∥-∥₁ : Map (eff ∥_∥₁)
  Map-∥-∥₁ .map f = rec (hlevel 1) (∣_∣₁ ∘ f)
