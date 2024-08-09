{-# OPTIONS --safe #-}
module Data.Nat.Path where

open import Foundations.Prelude

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects

open import Data.Nat.Base

private variable m n : ℕ

suc-inj : suc m ＝ suc n → m ＝ n
suc-inj = ap pred

instance
  Reflects-ℕ-Path : Reflects (m ＝ n) (m == n)
  Reflects-ℕ-Path {0}     {0}     = ofʸ refl
  Reflects-ℕ-Path {0}     {suc n} = ofⁿ λ p → ¬-so-false $ subst So (ap is-zero? p) oh
  Reflects-ℕ-Path {suc m} {0}     = ofⁿ λ p → ¬-so-false $ subst So (ap is-positive? p) oh
  Reflects-ℕ-Path {suc m} {suc n} =
    Reflects.dmap (ap suc) (λ m≠n sm=sn → ⊥.rec (m≠n (suc-inj sm=sn))) (Reflects-ℕ-Path {m} {n})

ℕ-identity-system : is-identity-system (λ m n → ⌞ m == n ⌟) _
ℕ-identity-system = reflects-path→identity-system!

instance
  H-Level-ℕ : H-Level (2 + n) ℕ
  H-Level-ℕ = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel! 1 ℕ-identity-system
  {-# OVERLAPPING H-Level-ℕ #-}

opaque
  suc≠zero : suc m ≠ 0
  suc≠zero = false!

opaque
  zero≠suc : 0 ≠ suc m
  zero≠suc = false!

opaque
  id≠suc : m ≠ suc m
  id≠suc {0}     = zero≠suc
  id≠suc {suc _} = id≠suc ∘ suc-inj

opaque
  id≠plus-suc : n ≠ n + suc m
  id≠plus-suc {0}     = zero≠suc
  id≠plus-suc {suc n} = id≠plus-suc ∘ suc-inj
