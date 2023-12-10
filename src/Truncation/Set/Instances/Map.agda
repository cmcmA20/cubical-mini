{-# OPTIONS --safe #-}
module Truncation.Set.Instances.Map where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Map

open import Truncation.Set.Base

instance
  Map-∥-∥₂ : Map (eff ∥_∥₂)
  Map-∥-∥₂ .map f = rec (hlevel 2) (∣_∣₂ ∘ f)
