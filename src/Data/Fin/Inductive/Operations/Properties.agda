{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Operations.Properties where

open import Meta.Prelude

open import Data.Empty
open import Data.Reflects.Base
open import Data.Nat.Order.Base
open import Data.Fin.Inductive as Fin
open import Data.Fin.Inductive.Operations

private variable
  ℓ ℓ′ ℓ″ : Level
  n : ℕ

ℕ→fin→ℕ : (k : ℕ) → (k< : k < n) → fin→ℕ (ℕ→fin k k<) ＝ k
ℕ→fin→ℕ {n = zero}   k      k< = false! k<
ℕ→fin→ℕ {n = suc n}  zero   _  = refl
ℕ→fin→ℕ {n = suc n} (suc k) k< = ap suc (ℕ→fin→ℕ k (<-peel k<))

fin→ℕ-fmax : (f : Fin n) → fin→ℕ f < fin→ℕ (fmax {n = n})
fin→ℕ-fmax {n = suc n}  fzero   = z<s
fin→ℕ-fmax {n = suc n} (fsuc f) = s<s (fin→ℕ-fmax f)

fin→ℕ-fmax0 : (z< : 0 < n) → (f : Fin n) → fin→ℕ f ≤ fin→ℕ (fmax0 z<)
fin→ℕ-fmax0 {n = suc n} z<  fzero   = z≤
fin→ℕ-fmax0 {n = suc n} z< (fsuc f) = <≃suc≤ ⁻¹ $ fin→ℕ-fmax f
