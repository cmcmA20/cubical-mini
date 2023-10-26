{-# OPTIONS --safe #-}
module Data.FinSub.Base where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Sigma

open import Meta.Record

open import Correspondences.Erased

import Data.Empty.Base as ⊥
open import Data.Nat.Base
  using (ℕ; zero; suc)
open import Data.Nat.Order.Computational

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

fin-ext : {k₁ k₂ : Fin n} → k₁ .index ＝ k₂ .index → k₁ ＝ k₂
fin-ext {n} = ap e.from ∘ Σ-prop-path (λ _ → ∥-∥ᴱ-is-prop (<-is-prop {n = n})) where
  module e = Equiv (iso→equiv fin-iso)
