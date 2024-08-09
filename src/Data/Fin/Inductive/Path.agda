{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Empty.Base as ⊥
open import Data.Fin.Inductive.Base as Fin
open import Data.Nat.Base
open import Data.Reflects.Base as Reflects
open import Data.Unit.Base

private variable
  @0 m n : ℕ
  k l : Fin m

fsuc-inj : {k l : Fin m} → fsuc k ＝ fsuc l → k ＝ l
fsuc-inj {m} {k} = ap pred′ where
  pred′ : Fin (suc m) → Fin m
  pred′ fzero    = k
  pred′ (fsuc x) = x

instance
  Reflects-Fin-Path : {k l : Fin n} → Reflects (k ＝ l) (fin→ℕ k == fin→ℕ l)
  Reflects-Fin-Path {k = fzero}  {(fzero)} = ofʸ refl
  Reflects-Fin-Path {k = fzero}  {fsuc l}  = ofⁿ (λ p → subst (Fin.rec ⊤ λ _ _ → ⊥) p tt)
  Reflects-Fin-Path {k = fsuc k} {(fzero)} = ofⁿ (λ p → subst (Fin.rec ⊤ λ _ _ → ⊥) (p ⁻¹) tt)
  Reflects-Fin-Path {k = fsuc k} {fsuc l}  = Reflects.dmap (ap fsuc) (contra fsuc-inj) Reflects-Fin-Path

  Fin-is-discrete : is-discrete (Fin n)
  Fin-is-discrete = reflects-path→is-discrete!

Extensional-Fin : Extensional (Fin n) 0ℓ
Extensional-Fin = reflects-path→extensional!

opaque
  fzero≠fsuc : fzero ≠ fsuc k
  fzero≠fsuc = false!

opaque
  fsuc≠fzero : fsuc k ≠ fzero
  fsuc≠fzero = false!

fin0-is-initial : Fin 0 ≃ ⊥
fin0-is-initial .fst ()
fin0-is-initial .snd .equiv-proof ()

fin1-is-contr : is-contr (Fin 1)
fin1-is-contr .fst = fzero
fin1-is-contr .snd fzero = refl

instance opaque
  H-Level-Fin0 : ∀{k} → ⦃ k ≥ʰ 1 ⦄ → H-Level k (Fin 0)
  H-Level-Fin0 ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (≃→is-of-hlevel! 1 fin0-is-initial)
  {-# OVERLAPPING H-Level-Fin0 #-}

instance
  H-Level-Fin1 : ∀{k} → H-Level k (Fin 1)
  H-Level-Fin1 = hlevel-basic-instance 0 fin1-is-contr
  {-# OVERLAPPING H-Level-Fin1 #-}
