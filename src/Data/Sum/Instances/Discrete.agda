{-# OPTIONS --safe #-}
module Data.Sum.Instances.Discrete where

open import Foundations.Base

open import Correspondences.Nullary.Decidable

import Data.Dec.Base as Dec
open Dec

open import Data.Sum.Path public

instance
  ⊎-is-discrete
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ is-discrete A ⦄ → ⦃ is-discrete B ⦄ → is-discrete (A ⊎ B)
  ⊎-is-discrete = is-discrete-η go where
    go : _
    go (inl x₁) (inl x₂) =
      Dec.map (ap inl) (λ w z → w (inl-inj z)) (x₁ ≟ x₂)
    go (inl x)  (inr y)  = no ⊎-disjoint
    go (inr y)  (inl x)  = no λ p → ⊎-disjoint (sym p)
    go (inr y₁) (inr y₂) =
      Dec.map (ap inr) (λ w z → w (inr-inj z)) (y₁ ≟ y₂)
