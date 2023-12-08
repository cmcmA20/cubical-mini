{-# OPTIONS --safe #-}
module Truncation.Set.Instances.Map where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Map

open import Truncation.Set.Base

instance
  Map-∥-∥₂ : Map (eff ∥_∥₂)
  Map-∥-∥₂ .Map.map {A} {B} = go where
    go : (A → B) → (∥ A ∥₂ → ∥ B ∥₂)
    go f = rec (hlevel 2) (∣_∣₂ ∘ f)
