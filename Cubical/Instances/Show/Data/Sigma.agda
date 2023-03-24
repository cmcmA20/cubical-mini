{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.Sigma where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.Base

open import Cubical.Instances.Show.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : A → Type ℓ′

instance
  ShowΣ : ⦃ Show A ⦄ → ⦃ {a : A} → Show (B a) ⦄ → Show (Σ A B)
  Show.show ShowΣ (a , b) = show a ++ (" , " ++ show b)
