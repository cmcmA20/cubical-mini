{-# OPTIONS --safe #-}
module Correspondences.Base where

open import Foundations.Base

open import Structures.n-Type

open import Data.Nat.Base
open import Data.Product.Base

Corr
  : (n : ℕ) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ (ℓsuc ℓ′) n)
Corr n ℓ′ A = functionₓ n A (Type ℓ′)

Rel
  : (n : ℕ) (ℓ′ : Level)
    {ℓ : Level} (A : Type ℓ)
  → Type (Levelₓ ℓ (ℓsuc ℓ′) n)
Rel n ℓ′ A = functionₓ n A (Prop ℓ′)

Pred : (ℓ′ : Level) {ℓ : Level} (A : Type ℓ) → Type (ℓ ⊔ ℓsuc ℓ′)
Pred = Corr 1

Pred₁ : (ℓ′ : Level) {ℓ : Level} (A : Type ℓ) → Type (ℓ ⊔ ℓsuc ℓ′)
Pred₁ = Rel 1
