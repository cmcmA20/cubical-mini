{-# OPTIONS --safe #-}
module Data.Truncation.Set.Instances.Idiom where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Idiom

open import Data.Truncation.Set.Base
open import Data.Truncation.Set.Instances.Map public

instance
  Idiom-∥-∥₂ : Idiom (eff ∥_∥₂)
  Idiom-∥-∥₂ .pure = ∣_∣₂
  Idiom-∥-∥₂ ._<*>_ ∣f∣₂ ∣a∣₂ =
    rec (hlevel 2) (_<$> ∣a∣₂) ∣f∣₂
