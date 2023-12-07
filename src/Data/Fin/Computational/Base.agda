{-# OPTIONS --safe #-}
module Data.Fin.Computational.Base where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Record

open import Correspondences.Erased

import Data.Empty.Base as ⊥
open import Data.Fin.Interface
open import Data.Nat.Base
  using (ℕ; zero; suc ; pred)
open import Data.Nat.Order.Computational
open import Data.Sum.Base

private variable
  ℓ ℓ′ : Level
  @0 m n : ℕ

record Fin (@0 n : ℕ) : Type where
  constructor mk-fin
  field
    index     : ℕ
    { bound } : ∥ index < n ∥ᴱ

open Fin

unquoteDecl fin-iso = declare-record-iso fin-iso (quote Fin)

fzero : Fin (suc n)
fzero = mk-fin 0

fsuc : Fin n → Fin (suc n)
fsuc (mk-fin k {(b)}) = mk-fin (suc k) {b}

fsplit
  : (k : Fin (suc n))
  → (k ＝ fzero) ⊎ (Σ[ l ꞉ Fin n ] (k ＝ fsuc l))
fsplit (mk-fin zero) = inl refl
fsplit (mk-fin (suc k) {(b)}) = inr ((mk-fin k {b}) , refl)

-- TODO can be strengthened
elim  : Π[ P ꞉ ∀ᴱ[ n ꞉ ℕ ] (Fin n → Type ℓ′) ]
        Π[ fz ꞉ ∀ᴱ[ n ꞉ ℕ ] P {suc n} fzero ]
        Π[ fs ꞉ ∀ᴱ[ n ꞉ ℕ ] ∀[ k ꞉ Fin n ] (P k → P (fsuc k)) ]
        ∀[ n ꞉ ℕ ] Π[ k ꞉ Fin n ] P k
elim P fz fs {x = suc n} k with fsplit k
... | inl p = subst P (sym p) fz
... | inr (l , p) = subst P (sym p) (fs (elim P fz fs l))

fpred : Fin (suc (suc n)) → Fin (suc n)
fpred = [ (λ _ → fzero) , fst ]ᵤ ∘ fsplit

impl : FinI Fin
impl .FinI.fzero = fzero
impl .FinI.fsuc = fsuc
impl .FinI.fsplit = fsplit
impl .FinI.elim = elim

fin→ℕ : Fin n → ℕ
fin→ℕ (mk-fin k) = k

module _ where
  open import Data.Fin.Base
    renaming (Fin to Finᵈ; fzero to fzeroᵈ; fsuc to fsucᵈ)

  default≃computational : ∀{n} → Finᵈ n ≃ Fin n
  default≃computational = iso→equiv $ to , iso from ri li where
    to : ∀{n} → Finᵈ n → Fin n
    to {suc _} fzeroᵈ    = fzero
    to {suc _} (fsucᵈ k) = fsuc (to k)

    from : ∀{n} → Fin n → Finᵈ n
    from {suc _} (mk-fin 0)                   = fzeroᵈ
    from {suc _} (mk-fin (suc k) {bound = b}) = fsucᵈ (from (mk-fin k {b}))

    ri : ∀{n} k → to {n} (from k) ＝ k
    ri {suc _} (mk-fin 0)       = refl
    ri {suc _} (mk-fin (suc k)) = ap fsuc (ri (mk-fin k))

    li : ∀{n} k → from {n} (to k) ＝ k
    li {suc _} fzeroᵈ    = refl
    li {suc _} (fsucᵈ k) = ap fsucᵈ (li k)

  module default≃computational {n} = Equiv (default≃computational {n})
