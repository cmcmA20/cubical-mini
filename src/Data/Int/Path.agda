{-# OPTIONS --safe #-}
module Data.Int.Path where

open import Foundations.Prelude

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Int.Base
open import Data.Reflects.Base as Reflects

_int=?_ : ℤ → ℤ → Bool
pos m    int=? pos n    = m == n
pos _    int=? negsuc _ = false
negsuc m int=? pos n    = false
negsuc m int=? negsuc n = m == n

private variable
  k l : ℤ
  m n : ℕ

pos-inj : pos m ＝ pos n → m ＝ n
pos-inj = ap ℤ→ℕ

negsuc-inj : negsuc m ＝ negsuc n → m ＝ n
negsuc-inj = suc-inj ∘ ap ℤ→ℕ

instance
  Reflects-ℤ-Path : Reflects (k ＝ l) (k int=? l)
  Reflects-ℤ-Path {pos _}    {pos _}    = Reflects.dmap (ap pos) (contra pos-inj) auto
  Reflects-ℤ-Path {pos m}    {negsuc n} = ofⁿ λ p → ¬-so-false $ subst So (ap is-negative? (p ⁻¹)) oh
  Reflects-ℤ-Path {negsuc m} {pos n}    = ofⁿ λ p → ¬-so-false $ subst So (ap is-negative? p) oh
  Reflects-ℤ-Path {negsuc m} {negsuc n} = Reflects.dmap (ap negsuc) (contra negsuc-inj) auto

  ℤ-is-discrete : is-discrete ℤ
  ℤ-is-discrete = reflects-path→is-discrete!
  {-# OVERLAPPING ℤ-is-discrete #-}

ℤ-identity-system : is-identity-system (λ k l → ⌞ k int=? l ⌟) _
ℤ-identity-system = reflects-path→identity-system!

instance
  H-Level-ℤ : H-Level (2 + n) ℤ
  H-Level-ℤ = hlevel-basic-instance 2 $ identity-system→is-of-hlevel! 1 ℤ-identity-system
  {-# OVERLAPPING H-Level-ℤ #-}

opaque
  pos≠negsuc : pos m ≠ negsuc n
  pos≠negsuc = false!

opaque
  negsuc≠pos : negsuc n ≠ pos m
  negsuc≠pos = false!
