{-# OPTIONS --safe #-}
module Truncation.Propositional.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Truncation.Propositional.Base as ∥-∥₁
open import Data.List.Base

∥-∥₁-decision : ∀{ℓ} {A : Type ℓ} → Dec A → Dec ∥ A ∥₁
∥-∥₁-decision = Dec.rec (λ z → yes ∣ z ∣₁) (λ x → no (∥-∥₁.rec ⊥-is-prop x))

instance
  decomp-dec-∥-∥₁ : ∀{ℓ} {A : Type ℓ} → goal-decomposition (quote Dec) ∥ A ∥₁
  decomp-dec-∥-∥₁ = decomp (quote ∥-∥₁-decision) [ `search (quote Dec) ]
