{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Base where

open import Foundations.Base
open import Foundations.Equiv

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
  : {P : ∀ {@0 n} → Fin n → Type ℓ}
  → (∀ {@0 n} → P {suc n} fzero)
  → (∀ {@0 n} (k : Fin n) → P k → P (fsuc k))
  → ∀ {@0 n} (k : Fin n) → P k
elim pfzero pfsuc fzero    = pfzero
elim pfzero pfsuc (fsuc x) = pfsuc x (elim pfzero pfsuc x)

rec : {A : Type ℓ}
      (a₀ : A) (aₛ : ∀{@0 n} → Fin n → A → A)
    → ∀ {@0 n} → Fin n → A
rec a₀ = elim a₀

squish : Fin n → Fin (suc n) → Fin n
squish fzero    fzero    = fzero
squish fzero    (fsuc j) = j
squish (fsuc i) fzero    = fzero
squish (fsuc i) (fsuc j) = fsuc (squish i j)

skip : Fin (suc n) → Fin n → Fin (suc n)
skip fzero    j        = fsuc j
skip (fsuc i) fzero    = fzero
skip (fsuc i) (fsuc j) = fsuc (skip i j)

fin→ℕ : Fin n → ℕ
fin→ℕ fzero    = 0
fin→ℕ (fsuc k) = suc (fin→ℕ k)

module _ where
  open import Data.Fin.Base
    renaming (Fin to Finᵈ; fzero to fzeroᵈ; fsuc to fsucᵈ)
  default≃inductive : ∀{n} → Finᵈ n ≃ Fin n
  default≃inductive = iso→equiv $ to , iso from ri li where
    to : ∀{n} → Finᵈ n → Fin n
    to {suc _} fzeroᵈ    = fzero
    to {suc _} (fsucᵈ k) = fsuc (to k)

    from : ∀{n} → Fin n → Finᵈ n
    from {suc _} fzero    = fzeroᵈ
    from {suc _} (fsuc k) = fsucᵈ (from k)

    ri : ∀{n} k → to {n} (from k) ＝ k
    ri {suc _} fzero    = refl
    ri {suc _} (fsuc _) = ap fsuc (ri _)

    li : ∀{n} k → from {n} (to k) ＝ k
    li {suc _} fzeroᵈ    = refl
    li {suc _} (fsucᵈ _) = ap fsucᵈ (li _)

  module default≃inductive {n} = Equiv (default≃inductive {n})
