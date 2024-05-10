{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Path where

open import Meta.Prelude

open import Data.Empty.Base as ⊥
open import Data.Fin.Inductive.Base

private variable
  @0 m n : ℕ
  k l : Fin m

fzero≠fsuc : fzero ≠ fsuc k
fzero≠fsuc p = subst discrim p tt where
  discrim : Fin m → Type
  discrim fzero    = ⊤
  discrim (fsuc _) = ⊥

fsuc≠fzero : fsuc k ≠ fzero
fsuc≠fzero = fzero≠fsuc ∘ sym

fsuc-inj : {k l : Fin m} → fsuc k ＝ fsuc l → k ＝ l
fsuc-inj {k} = ap pred′ where
  pred′ : Fin (suc _) → Fin _
  pred′ fzero    = k
  pred′ (fsuc x) = x

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
