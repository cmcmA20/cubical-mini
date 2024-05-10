{-# OPTIONS --safe #-}
module Data.Nat.Path where

open import Foundations.Prelude

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Empty.Base
open import Data.Unit.Base

open import Data.Nat.Base

private variable
  m n : ℕ

suc≠zero : suc m ≠ 0
suc≠zero p = subst is-positive p tt

zero≠suc : 0 ≠ suc m
zero≠suc = suc≠zero ∘ sym

suc-inj : suc m ＝ suc n → m ＝ n
suc-inj = ap pred

id≠suc : m ≠ suc m
id≠suc {0}     = zero≠suc
id≠suc {suc _} = id≠suc ∘ suc-inj

id≠plus-suc : n ≠ n + suc m
id≠plus-suc {0}     = zero≠suc
id≠plus-suc {suc n} = id≠plus-suc ∘ suc-inj

code-nat-refl : (m : ℕ) → is-true (m == m)
code-nat-refl zero    = tt
code-nat-refl (suc m) = code-nat-refl m

decode-nat : is-true (m == n) → m ＝ n
decode-nat {0}     {0}     _ = refl
decode-nat {suc m} {suc n}   = ap suc ∘ decode-nat

decode-nat-refl
  : (c : is-true (m == n))
  → ＜ code-nat-refl m ／ (λ i → is-true (m == decode-nat {m = m} c i)) ＼ c ＞
decode-nat-refl {0}     {0}     _ = refl
decode-nat-refl {suc m} {suc n}   = decode-nat-refl {m}

ℕ-identity-system : is-identity-system (λ m n → is-true (m == n)) code-nat-refl
ℕ-identity-system .to-path = decode-nat
ℕ-identity-system .to-path-over {a} = decode-nat-refl {a}

instance
  H-Level-ℕ : H-Level (2 + n) ℕ
  H-Level-ℕ = hlevel-basic-instance 2 $
    identity-system→is-of-hlevel 1 ℕ-identity-system λ _ _ → hlevel 1
  {-# OVERLAPPING H-Level-ℕ #-}
