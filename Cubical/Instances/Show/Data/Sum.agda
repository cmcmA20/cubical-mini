{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Sum where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum.Base

open import Cubical.Instances.Show.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

instance
  Show⊎ : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A ⊎ B)
  Show.show Show⊎ (inl x) = "inl " ++ show x
  Show.show Show⊎ (inr x) = "inr " ++ show x
