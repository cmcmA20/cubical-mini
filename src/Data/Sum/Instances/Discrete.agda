{-# OPTIONS --safe #-}
module Data.Sum.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base as Dec
open import Data.Sum.Path public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

⊎-is-discrete : is-discrete A → is-discrete B → is-discrete (A ⊎ B)
⊎-is-discrete A-di B-di = is-discrete-η λ where
  (inl a₁) (inl a₂) → Dec.map (ap inl) (_∘ inl-inj) $ is-discrete-β A-di a₁ a₂
  (inl _)  (inr _)  → no ⊎-disjoint
  (inr _)  (inl _)  → no $ ⊎-disjoint ∘ sym
  (inr b₁) (inr b₂) → Dec.map (ap inr) (_∘ inr-inj) (is-discrete-β B-di b₁ b₂)

instance
  decomp-dis-⊎ : goal-decomposition (quote is-discrete) (A ⊎ B)
  decomp-dis-⊎ = decomp (quote ⊎-is-discrete)
    [ `search (quote is-discrete) , `search (quote is-discrete) ]
