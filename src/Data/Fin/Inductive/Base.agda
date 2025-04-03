{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Base where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Bool.Base
  using (false; true)
open import Data.Fin.Interface
open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc)
  public
open import Data.Reflects.Base
open import Data.Sum.Base
  using (_⊎ₜ_; inl; inr)

private variable
  ℓ : Level
  @0 m n : ℕ

data Fin : @0 ℕ → Type where
  fzero :         Fin (suc n)
  fsuc  : Fin n → Fin (suc n)

weaken : Fin n → Fin (suc n)
weaken fzero    = fzero
weaken (fsuc k) = fsuc (weaken k)

fsplit : ∀ᴱ[ n ꞉ ℕ ] Π[ k ꞉ Fin (suc n) ]
         (k ＝ fzero) ⊎ (Σ[ k′ ꞉ Fin n ] (k ＝ fsuc k′))
fsplit fzero    = inl refl
fsplit (fsuc k) = inr (k , refl)

elim
  : (P : ∀ᴱ[ n ꞉ ℕ ] (Fin n → Type ℓ))
  → (∀ᴱ[ n ꞉ ℕ ] P {suc n} fzero)
  → (∀ᴱ[ n ꞉ ℕ ] ∀[ k ꞉ Fin n ] (P k → P (fsuc k)))
  → ∀ᴱ[ n ꞉ ℕ ] Π[ k ꞉ Fin n ] P k
elim _ fz _  fzero    = fz
elim P fz fs (fsuc k) = fs (elim P fz fs k)

impl : FinIᴱ Fin
impl .FinIᴱ.fzero = fzero
impl .FinIᴱ.fsuc = fsuc
impl .FinIᴱ.fsplit = fsplit
impl .FinIᴱ.elim = elim

rec = FinIᴱ.rec impl

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
  default≃inductive = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
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

instance
  Reflects-Fin-0 : Reflects (Fin 0) false
  Reflects-Fin-0 = ofⁿ λ ()

  Reflects-Fin-1 : Reflects (Fin 1) true
  Reflects-Fin-1 = ofʸ fzero
