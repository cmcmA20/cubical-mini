{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Path where

open import Meta.Prelude

open import Data.Empty.Base as ⊥
open import Data.Fin.Inductive.Base
open import Data.Nat.Base

private variable
  @0 m n : ℕ
  k l : Fin m

fzero≠fsuc : fzero ≠ fsuc k
fzero≠fsuc p = substₚ discrim p tt where
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

open import Foundations.IdentitySystem.Transport
open import Data.Nat.Path

fin-cast : {m n : ℕ} → m ＝ n → Fin m → Fin n
fin-cast {0}     {0}     _ = id
fin-cast {suc m} {suc n} _ fzero = fzero
fin-cast {suc m} {suc n} p (fsuc k) = fsuc (fin-cast (suc-inj p) k)
fin-cast {suc m} {0}     p = ⊥.rec (suc≠zero p)

fin-cast-coh : (m n : ℕ) (p : m ＝ n) (k : Fin m) → fin-cast p k ＝ substₚ (λ n → Fin n) p k
fin-cast-coh (suc m) = Jₚ> λ where
  fzero    → transport-refl _ ⁻¹
  (fsuc k) → ap fsuc (fin-cast-coh m m refl k ∙ transport-refl k) ∙ transport-refl _ ⁻¹

instance
  fin-transport-system : is-transport-system {B = λ n → Fin n} (erase path-identity-system)
  fin-transport-system .is-transport-system.subst     = fin-cast
  fin-transport-system .is-transport-system.subst-coh p b .erased = fin-cast-coh _ _ p b
