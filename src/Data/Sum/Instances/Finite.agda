{-# OPTIONS --safe #-}
module Data.Sum.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind

open import Correspondences.Nullary.Finite.Bishop

open import Data.Fin.Closure
open import Data.Sum.Properties

open import Truncation.Propositional

instance
  ⊎-is-fin-set
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ is-fin-set A ⦄ → ⦃ is-fin-set B ⦄ → is-fin-set (A ⊎ B)
  ⊎-is-fin-set = fin do
    aeq ← enumeration it
    beq ← enumeration it
    pure $ ⊎-ap aeq beq ∙ₑ fin-coproduct
