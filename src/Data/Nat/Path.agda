{-# OPTIONS --safe #-}
module Data.Nat.Path where

open import Foundations.Base

open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.Unit.Base

open import Data.Nat.Base public

private variable
  m n : ℕ

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

identity-system : is-identity-system Code code-refl
identity-system = set-identity-system code-is-prop (decode _ _)

instance
  H-Level-ℕ : ∀ {n} → H-Level (2 + n) ℕ
  H-Level-ℕ = hlevel-basic-instance 2 $ identity-system→is-of-hlevel 1 identity-system code-is-prop

suc≠zero : suc m ≠ 0
suc≠zero p = subst is-positive p tt

zero≠suc : 0 ≠ suc m
zero≠suc = suc≠zero ∘ sym

suc-inj : suc m ＝ suc n → m ＝ n
suc-inj = ap pred

neq-suc-id : (n : ℕ) → n ≠ suc n
neq-suc-id  zero   = zero≠suc
neq-suc-id (suc n) = neq-suc-id n ∘ suc-inj
