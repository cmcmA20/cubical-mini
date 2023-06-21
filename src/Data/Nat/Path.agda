{-# OPTIONS --safe #-}
module Data.Nat.Path where

open import Foundations.Base
open import Foundations.HLevel

open import Structures.IdentitySystem.Base

open import Data.Empty.Base

open import Data.Nat.Base public

private variable
  m n : ℕ

-- only to illustrate the method
module ℕ-path-code where

  Code : ℕ → ℕ → Type
  Code zero    zero    = ⊤
  Code zero    (suc _) = ⊥
  Code (suc _) zero    = ⊥
  Code (suc m) (suc n) = Code m n

  code-refl : (m : ℕ) → Code m m
  code-refl zero    = tt
  code-refl (suc m) = code-refl m

  decode : ∀ m n → Code m n → m ＝ n
  decode zero    zero    _ = refl
  decode (suc m) (suc n) c = ap suc (decode m n c)

  opaque
    unfolding is-of-hlevel
    code-is-prop : ∀ m n → is-prop (Code m n)
    code-is-prop zero    zero    _ _ = refl
    code-is-prop (suc m) (suc n) = code-is-prop m _

  ℕ-identity-system : is-identity-system Code code-refl
  ℕ-identity-system = set-identity-system code-is-prop (decode _ _)

ℕ-is-set : is-set ℕ
ℕ-is-set = identity-system→hlevel 1 ℕ-path-code.ℕ-identity-system ℕ-path-code.code-is-prop

suc≠zero : ¬ suc m ＝ 0
suc≠zero p = transport (ap discrim p) tt
  where
  discrim : ℕ → Type
  discrim 0       = ⊥
  discrim (suc _) = ⊤

suc-inj : suc m ＝ suc n → m ＝ n
suc-inj = ap pred
