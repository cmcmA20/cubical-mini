{-# OPTIONS --safe #-}
module Data.Sum.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete

import Data.Dec.Base as Dec

open import Data.Sum.Path public

instance
  Discrete-⊎
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ Discrete A ⦄ → ⦃ Discrete B ⦄ → Discrete (A ⊎ B)
  Discrete-⊎ .Discrete._≟_ (inl x₁) (inl x₂) =
    Dec.map (ap inl) (λ w z → w (inl-inj z)) (x₁ ≟ x₂)
  Discrete-⊎ .Discrete._≟_ (inl x)  (inr y)  = no ⊎-disjoint
  Discrete-⊎ .Discrete._≟_ (inr y)  (inl x)  = no λ p → ⊎-disjoint (sym p)
  Discrete-⊎ .Discrete._≟_ (inr y₁) (inr y₂) =
    Dec.map (ap inr) (λ w z → w (inr-inj z)) (y₁ ≟ y₂)
