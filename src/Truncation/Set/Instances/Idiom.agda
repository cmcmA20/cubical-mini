{-# OPTIONS --safe #-}
module Truncation.Set.Instances.Idiom where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Idiom

open import Truncation.Set.Base

instance
  Map-∥-∥₂ : Map (eff ∥_∥₂)
  Map-∥-∥₂ .Map._<$>_ = map

  Idiom-∥-∥₂ : Idiom (eff ∥_∥₂)
  Idiom-∥-∥₂ .Idiom.pure = ∣_∣₂
  Idiom-∥-∥₂ .Idiom._<*>_ ∣f∣₂ ∣a∣₂ =
    rec (hlevel 2) (_<$> ∣a∣₂) ∣f∣₂
