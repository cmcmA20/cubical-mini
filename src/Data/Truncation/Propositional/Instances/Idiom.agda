{-# OPTIONS --safe #-}
module Data.Truncation.Propositional.Instances.Idiom where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Idiom
open import Meta.Inductive

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Instances.Map public

instance
  Idiom-∥-∥₁ : Idiom (eff ∥_∥₁)
  Idiom-∥-∥₁ .pure = ∣_∣₁
  Idiom-∥-∥₁ ._<*>_ ∣f∣₁ ∣a∣₁ = rec! (_<$> ∣a∣₁) ∣f∣₁ where
    instance _ = hlevel-prop-instance squash₁
