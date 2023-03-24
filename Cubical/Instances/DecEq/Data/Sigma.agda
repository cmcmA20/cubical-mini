{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Data.Sigma where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Instances.DecEq.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : A → Type ℓ′

instance
  DecEqΣ : ⦃ DecEq A ⦄ → ⦃ {a : A} → DecEq (B a) ⦄ → DecEq (Σ A B)
  DecEq._≟_ DecEqΣ = discreteΣ _≟_ λ _ → _≟_
