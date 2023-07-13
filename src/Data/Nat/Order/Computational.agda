{-# OPTIONS --safe #-}
module Data.Nat.Order.Computational where

open import Foundations.Base
open import Foundations.HLevel

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Unit.Base

open import Data.Nat.Base

private variable
  m n k : ℕ

opaque
  _≤_ : ℕ → ℕ → Type
  zero  ≤ n = ⊤
  suc m ≤ suc n = m ≤ n
  suc m ≤ zero = ⊥

  z≤ : 0 ≤ n
  z≤ = tt

  s≤s : m ≤ n → suc m ≤ suc n
  s≤s = id

  ≤-peel : suc m ≤ suc n → m ≤ n
  ≤-peel = id

Positive : ℕ → Type
Positive zero    = ⊥
Positive (suc _) = ⊤

_<_ : ℕ → ℕ → Type
m < n = suc m ≤ n
infix 3 _<_ _≤_

_≥_ : ℕ → ℕ → Type
m ≥ n = n ≤ m

_>_ : ℕ → ℕ → Type
m > n = n < m

-- Properties of order

opaque
  unfolding _≤_
  ≤-refl : n ≤ n
  ≤-refl {0} = tt
  ≤-refl {suc n} = ≤-refl {n}

  ≤-trans : m ≤ n → n ≤ k → m ≤ k
  ≤-trans {0}     {_} _ _ = tt
  ≤-trans {suc m} {suc n} {suc k} p q = ≤-trans {m = m} p q

  ≤-antisym : m ≤ n → n ≤ m → m ＝ n
  ≤-antisym {0} {0} _ _ = refl
  ≤-antisym {suc m} {suc n} p q = ap suc (≤-antisym p q)

  opaque
    unfolding is-of-hlevel
    ≤-is-prop : is-prop (m ≤ n)
    ≤-is-prop {0} {_} _ _ = refl
    ≤-is-prop {suc m} {suc n} p q = ≤-is-prop {m} p q

  ≤-suc-r : m ≤ n → m ≤ suc n
  ≤-suc-r {0} {_} _ = tt
  ≤-suc-r {suc m} {suc n} p = ≤-suc-r {m} p

  ≤-ascend : n ≤ suc n
  ≤-ascend {n} = ≤-suc-r {m = n} (≤-refl {n})

  instance
    ≤-is-of-hlevel : is-of-hlevel (suc k) (m ≤ n)
    ≤-is-of-hlevel {m} = is-prop→is-of-hlevel-suc (≤-is-prop {m = m})

  ≤-dec : (m n : ℕ) → Dec (m ≤ n)
  ≤-dec zero _ = yes tt
  ≤-dec (suc _) zero = no id
  ≤-dec (suc m) (suc n) = ≤-dec m n

  ¬sucn≤n : ¬ (suc n ≤ n)
  ¬sucn≤n {suc n} p = ¬sucn≤n {n} p

  ¬sucn≤0 : ¬ (suc n ≤ 0)
  ¬sucn≤0 {(suc n)} = λ ()

  ≤-split : (m n : ℕ) → (m < n) ⊎ (n < m) ⊎ (m ＝ n)
  ≤-split m n with ≤-dec (suc m) n
  ... | yes m<n = inl m<n
  ... | no  m≥n with ≤-dec (suc n) m
  ... | yes n<m = inr $ inl n<m
  ... | no  n≥m = inr $ inr (go m n m≥n n≥m) where
    go : ∀ m n → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
    go zero zero _ _ = refl
    go zero (suc n) p _ = absurd (p tt)
    go (suc m) zero _ q = absurd (q tt)
    go (suc m) (suc n) p q = ap suc $ go m n p q
