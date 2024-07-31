{-# OPTIONS --safe #-}
module Meta.Variadic where

open import Foundations.Base

open import Data.HVec.Base public
open import Data.Nat.Base

-- Correspondence valued in arbitrary structure
SCorr
  : (arity : ℕ) {ls : Levels arity} (As : Types _ ls)
    {ℓ : Level} (U : Type ℓ) ⦃ u : Underlying U ⦄
  → Type (ℓ ⊔ ℓsup _ ls)
SCorr arity As U = Arrows arity As U

SCorr⁰ = SCorr 0
SCorr¹ = SCorr 1
SCorr² = SCorr 2
SCorr³ = SCorr 3
SCorr⁴ = SCorr 4
SCorr⁵ = SCorr 5

SPred = SCorr¹

-- Type-valued correspondence
Corr
  : (arity : ℕ) {ls : Levels arity} (As : Types _ ls) (ℓ : Level)
  → Type (ℓsuc ℓ ⊔ ℓsup _ ls)
Corr arity As ℓ = SCorr arity As (Type ℓ)

Corr⁰ = Corr 0
Corr¹ = Corr 1
Corr² = Corr 2
Corr³ = Corr 3
Corr⁴ = Corr 4
Corr⁵ = Corr 5

Pred = Corr¹

Variadic¹ : Typeω
Variadic¹ =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U
  → Corr  _ As (u .ℓ-underlying)

Variadic-binding¹ : Typeω
Variadic-binding¹ =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U
  → Type (u .ℓ-underlying ⊔ ℓsup _ ls)

Quantⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → (∀ {ℓᵃ ℓᵇ} (A : Type ℓᵃ) → (A → Type ℓᵇ) → Type (ℓᵃ ⊔ ℓᵇ))
  → SCorr _ As U
  → Type (u .ℓ-underlying ⊔ ℓsup _ ls)
Quantⁿ {0}           Q T = ⌞ T ⌟
Quantⁿ {1}           Q T = Q _ λ x → ⌞ T x ⌟
Quantⁿ {suc (suc _)} Q T = Q _ λ x → Quantⁿ Q (T x)

Universalⁿ : Variadic-binding¹
Universalⁿ = Quantⁿ Π-syntax

IUniversalⁿ : Variadic-binding¹
IUniversalⁿ = Quantⁿ ∀-syntax

Existentialⁿ : Variadic-binding¹
Existentialⁿ = Quantⁿ Σ-syntax
