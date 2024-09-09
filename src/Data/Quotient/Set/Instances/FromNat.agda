{-# OPTIONS --safe #-}
module Data.Quotient.Set.Instances.FromNat where

open import Foundations.Base

open import Meta.Literals.FromNat

open import Data.Quotient.Set.Base

instance
  From-ℕ-/₂
    : ∀{ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′}
    → ⦃ nl : From-ℕ A ⦄ → From-ℕ (A / R)
  From-ℕ-/₂ {ℓ′} ⦃ nl ⦄ .From-ℕ.Constraint n = Lift ℓ′ (nl .From-ℕ.Constraint n)
  From-ℕ-/₂ ⦃ nl ⦄ .from-ℕ n ⦃ (c) ⦄ = ⦋ nl .from-ℕ n ⦃ c .lower ⦄ ⦌
