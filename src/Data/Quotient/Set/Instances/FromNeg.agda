{-# OPTIONS --safe #-}
module Data.Quotient.Set.Instances.FromNeg where

open import Foundations.Base

open import Meta.Literals.FromNeg

open import Data.Quotient.Set.Base

instance
  From-neg-/₂
    : ∀{ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′}
    → ⦃ nl : From-neg A ⦄ → From-neg (A / R)
  From-neg-/₂ {ℓ′} ⦃ nl ⦄ .From-neg.Constraint n = Lift ℓ′ (nl .From-neg.Constraint n)
  From-neg-/₂ ⦃ nl ⦄ .from-neg n ⦃ (c) ⦄ = ⦋ nl .from-neg n ⦃ c .lower ⦄ ⦌
