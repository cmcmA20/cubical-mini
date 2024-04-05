{-# OPTIONS --safe #-}
module Data.Nat.Path where

open import Foundations.Base
open import Foundations.HLevel

open import Structures.IdentitySystem.Base

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


Code : ℕ → ℕ → Type
Code m n = is-true (m == n)

code-refl : (m : ℕ) → Code m m
code-refl 0       = tt
code-refl (suc m) = code-refl m

decode : ∀ m n → Code m n → m ＝ n
decode 0       0       _ = refl
decode 0       (suc _) p = absurd p
decode (suc _) 0       p = absurd p
decode (suc _) (suc _) = ap suc ∘ decode _ _

code-is-prop : ∀ m n → is-prop (Code m n)
code-is-prop 0       0       = hlevel 1
code-is-prop 0       (suc _) = hlevel 1
code-is-prop (suc _) 0       = hlevel 1
code-is-prop (suc m) (suc _) = code-is-prop m _

identity-system : is-identity-system Code code-refl
identity-system = set-identity-system code-is-prop (decode _ _)

ℕ-is-set : is-set ℕ
ℕ-is-set = identity-system→is-of-hlevel 1 identity-system code-is-prop

ℕ-is-of-hlevel : ∀ n → is-of-hlevel (2 + n) ℕ
ℕ-is-of-hlevel n = is-of-hlevel-+-left 2 n ℕ-is-set

instance
  H-Level-ℕ : H-Level (2 + n) ℕ
  H-Level-ℕ = hlevel-basic-instance 2 ℕ-is-set
