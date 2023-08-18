{-# OPTIONS --safe #-}
module Data.Nat.Path where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.Unit.Instances.HLevel

open import Data.Nat.Base public

private variable
  m n : ℕ

-- only to illustrate the method
module ℕ-path-code-naive where private

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

  code-is-prop : ∀ m n → is-prop (Code m n)
  code-is-prop 0       0       = hlevel!
  code-is-prop 0       (suc _) = hlevel!
  code-is-prop (suc _) 0       = hlevel!
  code-is-prop (suc m) (suc _) = code-is-prop m _

  ℕ-identity-system : is-identity-system Code code-refl
  ℕ-identity-system = set-identity-system code-is-prop (decode _ _)

module ℕ-path-code where

  Code : ℕ → ℕ → Type
  Code m n = ⟦ m == n ⟧ᵇ

  code-refl : (m : ℕ) → Code m m
  code-refl 0       = tt
  code-refl (suc m) = code-refl m

  decode : ∀ m n → Code m n → m ＝ n
  decode 0       0       _ = refl
  decode 0       (suc n) p = absurd p
  decode (suc m) 0       p = absurd p
  decode (suc m) (suc n) = ap suc ∘ decode _ _

  code-is-prop : ∀ m n → is-prop (Code m n)
  code-is-prop 0       0       = hlevel!
  code-is-prop 0       (suc n) = hlevel!
  code-is-prop (suc m) 0       = hlevel!
  code-is-prop (suc m) (suc n) = code-is-prop m _

  ℕ-identity-system : is-identity-system Code code-refl
  ℕ-identity-system = set-identity-system code-is-prop (decode _ _)

instance
  ℕ-is-set : is-set ℕ
  ℕ-is-set = identity-system→hlevel 1 ℕ-path-code.ℕ-identity-system ℕ-path-code.code-is-prop

ℕ-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) ℕ
ℕ-is-of-hlevel n = is-of-hlevel-+-left 2 n ℕ-is-set

suc≠zero : suc m ≠ 0
suc≠zero p = subst is-positive p tt

suc-inj : suc m ＝ suc n → m ＝ n
suc-inj = ap pred
