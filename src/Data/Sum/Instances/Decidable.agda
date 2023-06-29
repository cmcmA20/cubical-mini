{-# OPTIONS --safe #-}
module Data.Sum.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Bool.Base
import Data.Dec.Base as Dec
open Dec
open import Data.List.Base
open import Data.Sum.Path public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

opaque
  unfolding is-decidable-at-hlevel
  ⊎-is-discrete : is-discrete A → is-discrete B → is-discrete (A ⊎ B)
  ⊎-is-discrete di _ (inl x₁) (inl x₂) =
    Dec.map (ap inl) (_∘ inl-inj) (di x₁ x₂)
  ⊎-is-discrete _ _ (inl _) (inr _) = no ⊎-disjoint
  ⊎-is-discrete _ _ (inr _) (inl _) = no $ ⊎-disjoint ∘ sym
  ⊎-is-discrete _ di (inr y₁) (inr y₂) =
    Dec.map (ap inr) (_∘ inr-inj) (di y₁ y₂)

  ⊎-decision : Decision A → Decision B → Decision (A ⊎ B)
  ⊎-decision da db .does = da .does or db .does
  ⊎-decision (yes a) _ .proof = ofʸ (inl a)
  ⊎-decision (no ¬a) (yes b) .proof = ofʸ (inr b)
  ⊎-decision (no ¬a) (no ¬b) .proof = ofⁿ [ ¬a , ¬b ]ᵤ

instance
  decomp-dec₁-⊎ : goal-decomposition (quote is-decidable-at-hlevel) (A ⊎ B)
  decomp-dec₁-⊎ = decomp (quote ⊎-is-discrete)
    (`search (quote is-decidable-at-hlevel) ∷ `search (quote is-decidable-at-hlevel) ∷ [])

  decomp-dec₀-⊎ : goal-decomposition (quote is-decidable-at-hlevel) (A ⊎ B)
  decomp-dec₀-⊎ = decomp (quote ⊎-decision)
    (`search (quote is-decidable-at-hlevel) ∷ `search (quote is-decidable-at-hlevel) ∷ [])
