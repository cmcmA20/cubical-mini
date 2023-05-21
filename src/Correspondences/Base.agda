{-# OPTIONS --safe #-}
module Correspondences.Base where

open import Foundations.Base
open import Data.Nat.Base

open import Data.Product

Corr : (n : ℕ) (ℓ′ : Level) {ℓ : Level} (A : Type ℓ) → Type (Levelₓ ℓ (ℓsuc ℓ′) n)
Corr n ℓ′ A = functionₓ n A (Type ℓ′)

Pred : {ℓ : Level} (A : Type ℓ) (ℓ′ : Level) → Type (ℓ ⊔ ℓsuc ℓ′)
Pred A ℓ′ = Corr 1 ℓ′ A
