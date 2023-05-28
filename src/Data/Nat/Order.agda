{-# OPTIONS --safe #-}
module Data.Nat.Order where

open import Foundations.Base

open import Meta.HLevel

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Unit.Base

open import Data.Nat.Base

private variable
  m n k : ℕ

data _≤_ : ℕ → ℕ → Type where
  instance
    z≤ : 0 ≤ n
  s≤s : m ≤ n → suc m ≤ suc n

instance
  s≤s′ : ⦃ p : m ≤ n ⦄ → suc m ≤ suc n
  s≤s′ ⦃ p ⦄ = s≤s p

Positive : ℕ → Type
Positive zero    = ⊥
Positive (suc _) = ⊤

_<_ : ℕ → ℕ → Type
m < n = suc m ≤ n
infix 3 _<_ _≤_


-- Properties of order

≤-refl : n ≤ n
≤-refl {(zero)} = z≤
≤-refl {suc n}  = s≤s ≤-refl

≤-trans : m ≤ n → n ≤ k → m ≤ k
≤-trans z≤      z≤      = z≤
≤-trans z≤      (s≤s q) = z≤
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-antisym : m ≤ n → n ≤ m → m ＝ n
≤-antisym z≤      z≤      = refl
≤-antisym (s≤s p) (s≤s q) = ap suc (≤-antisym p q)

≤-is-prop : is-prop (m ≤ n)
≤-is-prop z≤      z≤      = refl
≤-is-prop (s≤s p) (s≤s q) = ap s≤s (≤-is-prop p q)

≤-peel : suc m ≤ suc n → m ≤ n
≤-peel (s≤s p) = p

≤-suc-r : m ≤ n → m ≤ suc n
≤-suc-r z≤      = z≤
≤-suc-r (s≤s p) = s≤s (≤-suc-r p)

≤-ascend : n ≤ suc n
≤-ascend = ≤-suc-r ≤-refl

instance
  H-Level-≤ : H-Level (suc k) (m ≤ n)
  H-Level-≤ = prop-instance ≤-is-prop

≤-dec : (m n : ℕ) → Dec (m ≤ n)
≤-dec zero zero = yes z≤
≤-dec zero (suc y) = yes z≤
≤-dec (suc x) zero = no λ { () }
≤-dec (suc x) (suc y) with ≤-dec x y
... | yes x≤y = yes (s≤s x≤y)
... | no ¬x≤y = no (λ { (s≤s x≤y) → ¬x≤y x≤y })

¬sucn≤n : ¬ (suc n ≤ n)
¬sucn≤n {(suc n)} (s≤s ord) = ¬sucn≤n ord

≤-split : (m n : ℕ) → (m < n) ⊎ (n < m) ⊎ (m ＝ n)
≤-split m n with ≤-dec (suc m) n
≤-split m n | yes m<n = inl m<n
≤-split m n | no m≥n with ≤-dec (suc n) m
≤-split m n | no m≥n | yes n<m = inr (inl n<m)
≤-split m n | no m≥n | no n≥m  = inr (inr (go m n m≥n n≥m)) where
  go : ∀ m n → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
  go zero zero p q          = refl
  go zero (suc zero) p q    = absurd (p (s≤s z≤))
  go zero (suc (suc n)) p q = absurd (p (s≤s z≤))
  go (suc zero) zero p q    = absurd (q (s≤s z≤))
  go (suc (suc m)) zero p q = absurd (q (s≤s z≤))
  go (suc m) (suc n) p q    = ap suc (go m n (λ { a → p (s≤s a) }) λ { a → q (s≤s a) })
