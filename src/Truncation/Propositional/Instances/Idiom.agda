{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.Idiom where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Idiom

open import Truncation.Propositional.Base
open import Truncation.Propositional.Instances.Map public

instance
  Idiom-∥-∥₁ : Idiom (eff ∥_∥₁)
  Idiom-∥-∥₁ .pure = ∣_∣₁
  Idiom-∥-∥₁ ._<*>_ ∣f∣₁ ∣a∣₁ =
    rec (hlevel 1) (_<$> ∣a∣₁) ∣f∣₁
