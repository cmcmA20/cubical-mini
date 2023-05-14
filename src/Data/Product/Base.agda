{-# OPTIONS --safe #-}
module Data.Product.Base where

open import Foundations.Base
open import Data.Nat.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

Levelₓ : Level → Level → ℕ → Level
Levelₓ ℓ₁ ℓ₂ zero    = ℓ₂
Levelₓ ℓ₁ ℓ₂ (suc n) = ℓ₁ ⊔ (Levelₓ ℓ₁ ℓ₂ n)

functionₓ : (n : ℕ) → Type ℓ → Type ℓ′ → Type (Levelₓ ℓ ℓ′ n)
functionₓ zero    A B = B
functionₓ (suc n) A B = A → functionₓ n A B

Vecₓ : Type ℓ → ℕ → Type ℓ
Vecₓ A 0             = Lift _ ⊤
Vecₓ A 1             = A
Vecₓ A (suc (suc n)) = A × Vecₓ A (suc n)

-- rec
_$ₓ_ : ∀ {n} → functionₓ n A B → (Vecₓ A n → B)
_$ₓ_ {n = 0          } xs _ = xs
_$ₓ_ {n = 1          } xs   = xs
_$ₓ_ {n = suc (suc n)} f xs = f (xs .fst) $ₓ xs .snd
