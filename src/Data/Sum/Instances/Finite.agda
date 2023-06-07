{-# OPTIONS --safe #-}
module Data.Sum.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind
open import Meta.Finite

open import Data.Fin.Closure
open import Data.Sum.Properties

open import Truncation.Propositional

instance
  Finite-⊎
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → ⦃ Finite A ⦄ → ⦃ Finite B ⦄ → Finite (A ⊎ B)
  Finite-⊎ {A} {B} = fin do
    aeq ← enumeration {T = A}
    beq ← enumeration {T = B}
    pure (⊎-ap aeq beq ∙ₑ fin-coproduct)
