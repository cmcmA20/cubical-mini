{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.Idiom where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Idiom

open import Truncation.Propositional.Base

instance
  Map-∥-∥₁ : Map (eff ∥_∥₁)
  Map-∥-∥₁ .Map._<$>_ = map

  Idiom-∥-∥₁ : Idiom (eff ∥_∥₁)
  Idiom-∥-∥₁ .Idiom.pure = ∣_∣₁
  Idiom-∥-∥₁ .Idiom._<*>_ ∣f∣₁ ∣a∣₁ =
    rec (hlevel 1) (_<$> ∣a∣₁) ∣f∣₁
