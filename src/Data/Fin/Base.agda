{-# OPTIONS --safe #-}
module Data.Fin.Base where

open import Foundations.Base

open import Data.Nat.Base public
  using (ℕ; zero; suc)

private variable
  ℓ : Level
  @0 m n : ℕ

data Fin : @0 ℕ → Type where
  fzero :         Fin (suc n)
  fsuc  : Fin n → Fin (suc n)

weaken : Fin n → Fin (suc n)
weaken fzero    = fzero
weaken (fsuc k) = fsuc (weaken k)

elim
  : (P : ∀ {n} → Fin n → Type ℓ)
  → (∀ {n} → P {suc n} fzero)
  → (∀ {n} (k : Fin n) → P k → P (fsuc k))
  → ∀ {n} (k : Fin n) → P k
elim P pfzero pfsuc {suc n} fzero = pfzero
elim P pfzero pfsuc {suc n} (fsuc x) = pfsuc x (elim P pfzero pfsuc x)

squish : Fin n → Fin (suc n) → Fin n
squish fzero fzero = fzero
squish fzero (fsuc j) = j
squish (fsuc i) fzero = fzero
squish (fsuc i) (fsuc j) = fsuc (squish i j)

skip : Fin (suc n) → Fin n → Fin (suc n)
skip fzero j = fsuc j
skip (fsuc i) fzero = fzero
skip (fsuc i) (fsuc j) = fsuc (skip i j)
