{-# OPTIONS --safe #-}
module Data.Fin.Computational.Path where

open import Meta.Prelude

open import Meta.Deriving.HLevel
open import Meta.Extensionality
open import Meta.Record

open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Empty.Base as ⊥
open import Data.Fin.Computational.Base
open import Data.Nat.Path
open import Data.Nat.Order.Inductive.Base

private variable @0 n : ℕ

open Fin

unquoteDecl fin-iso = declare-record-iso fin-iso (quote Fin)
unquoteDecl H-Level-Fin = declare-record-hlevel 2 H-Level-Fin (quote Fin)

fin-ext : {k₁ k₂ : Fin n} → k₁ .index ＝ k₂ .index → k₁ ＝ k₂
fin-ext {n} p = apˢ {A = Σ[ x ꞉ ℕ ] Erased (is-true (x <? n))} (≅→≃ fin-iso ⁻¹ $_) (p ,ₚ prop!)

module _ {ℓ} ⦃ sa : Extensional ℕ ℓ ⦄ where instance
  Extensional-Fin : Extensional (Fin n) ℓ
  Extensional-Fin .Pathᵉ (mk-fin u) (mk-fin v) = sa .Pathᵉ u v
  Extensional-Fin .reflᵉ (mk-fin k) = sa .reflᵉ k
  Extensional-Fin .idsᵉ .to-path = fin-ext ∘ sa .idsᵉ .to-path
  Extensional-Fin .idsᵉ .to-path-over = sa .idsᵉ .to-path-over

mk-fin-inj
  : ∀ {x y : ℕ} {b₁ b₂}
  → mk-fin {n} x {b₁}  ＝ mk-fin y {b₂} → x ＝ y
mk-fin-inj = ap index

fzero≠fsuc : ∀{k} → fzero {n} ≠ fsuc k
fzero≠fsuc = zero≠suc ∘ mk-fin-inj

fsuc≠fzero : ∀{k} → fsuc {n} k ≠ fzero
fsuc≠fzero = fzero≠fsuc ∘ sym

fsuc-inj : ∀ {k l} → fsuc {n} k ＝ fsuc l → k ＝ l
fsuc-inj = fin-ext ∘ suc-inj ∘ mk-fin-inj

instance
  H-Level-Fin0 : ∀ {k} → ⦃ k ≥ʰ 1 ⦄ → H-Level k (Fin 0)
  H-Level-Fin0 ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance λ ()
  {-# OVERLAPPING H-Level-Fin0 #-}

  H-Level-Fin1 : ∀ {k} → H-Level k (Fin 1)
  H-Level-Fin1 = hlevel-basic-instance 0 $ fzero , λ where
    (mk-fin zero) → refl
    (mk-fin (suc j) {(b)}) → ⊥.rec (b .erased)
  {-# OVERLAPPING H-Level-Fin1 #-}
