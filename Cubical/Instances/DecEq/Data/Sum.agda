{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Data.Sum where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum

open import Cubical.Instances.DecEq.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

instance
  DecEq⊎ : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (A ⊎ B)
  DecEq._≟_ DecEq⊎ = discrete⊎ _≟_ _≟_
