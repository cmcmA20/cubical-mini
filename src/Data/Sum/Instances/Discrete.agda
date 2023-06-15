{-# OPTIONS --safe #-}
module Data.Sum.Instances.Discrete where

open import Foundations.Base

open import Meta.Decision

import Data.Dec.Base as Dec
open Dec

open import Data.Sum.Path public

instance
  Discrete-⊎
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ Discrete A ⦄ → ⦃ Discrete B ⦄ → Discrete (A ⊎ B)
  Discrete-⊎ .Decision.has-decidable (inl x₁) (inl x₂) =
    Dec.map (ap inl) (λ w z → w (inl-inj z)) (x₁ ≟ x₂)
  Discrete-⊎ .Decision.has-decidable (inl x)  (inr y)  = no ⊎-disjoint
  Discrete-⊎ .Decision.has-decidable (inr y)  (inl x)  = no λ p → ⊎-disjoint (sym p)
  Discrete-⊎ .Decision.has-decidable (inr y₁) (inr y₂) =
    Dec.map (ap inr) (λ w z → w (inr-inj z)) (y₁ ≟ y₂)
