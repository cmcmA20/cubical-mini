{-# OPTIONS --safe #-}
module Data.Sum.Instances.Discrete where

open import Foundations.Base

open import Logic.Discreteness

open import Data.Dec.Base as Dec
open import Data.Sum.Base
open import Data.Sum.Path

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

instance
  ⊎-is-discrete : ⦃ A-di : is-discrete A ⦄ → ⦃ B-di : is-discrete B ⦄
                → is-discrete (A ⊎ B)
  ⊎-is-discrete {A} {B} = go _ _ where
    go : (x y : A ⊎ B) → Dec (x ＝ y)
    go (inl a₁) (inl a₂) = Dec.dmap (ap inl) (_∘ inl-inj) $ a₁ ≟ a₂
    go (inl _)  (inr _)  = no ⊎-disjoint
    go (inr _)  (inl _)  = no $ ⊎-disjoint ∘ sym
    go (inr b₁) (inr b₂) = Dec.dmap (ap inr) (_∘ inr-inj) (b₁ ≟ b₂)
