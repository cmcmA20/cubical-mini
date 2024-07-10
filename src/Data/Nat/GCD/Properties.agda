{-# OPTIONS --safe #-}
module Data.Nat.GCD.Properties where

open import Foundations.Base
open import Correspondences.Wellfounded

open import Data.Empty
open import Data.Sum
open import Data.Nat.Base
open import Data.Nat.Order.Inductive
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Inductive
open import Data.Nat.GCD

gcd-refl : ∀ x → gcd x x ＝ x
gcd-refl x with ≤-split x x
... | inl p       = absurd (¬sucn≤n p)
... | inr (inl p) = absurd (¬sucn≤n p)
... | inr (inr _) = refl

gcd′[m,n]∣m,n : ∀ {m n} rec n<m → (gcd′ m n rec n<m ∣ m) × (gcd′ m n rec n<m ∣ n)
gcd′[m,n]∣m,n {m} {n = zero}     _        _   = (∣-refl m) , (m ∣0)
gcd′[m,n]∣m,n {m} {n@(suc n-1)} (acc rec) n<m with gcd′[m,n]∣m,n (rec n n<m) (m%n<n m n (s≤s z≤))
... | dm , dn = ∣n∣m%n⇒∣m dm dn , dm

gcd′-greatest : ∀ {m n c} rec n<m → c ∣ m → c ∣ n → c ∣ gcd′ m n rec n<m
gcd′-greatest {m} {n = zero}     _        _   c∣m _   = c∣m
gcd′-greatest {m} {n@(suc n-1)} (acc rec) n<m c∣m c∣n =
  gcd′-greatest (rec n n<m) (m%n<n m n (s≤s z≤)) c∣n (%-presˡ-∣ c∣m c∣n)

gcd[m,n]∣m : ∀ m n → gcd m n ∣ m
gcd[m,n]∣m m n with ≤-split m n
... | inl  m<n      = gcd′[m,n]∣m,n (Wf-< n) m<n .snd
... | inr (inl n<m) = gcd′[m,n]∣m,n (Wf-< m) n<m .fst
... | inr (inr _)   = ∣-refl m

gcd[m,n]∣n : ∀ m n → gcd m n ∣ n
gcd[m,n]∣n m n with ≤-split m n
... | inl  m<n      = gcd′[m,n]∣m,n (Wf-< n) m<n .fst
... | inr (inl n<m) = gcd′[m,n]∣m,n (Wf-< m) n<m .snd
... | inr (inr e)   = subst (m ∣_) e (∣-refl m)

gcd-greatest : ∀ {m n c} → c ∣ m → c ∣ n → c ∣ gcd m n
gcd-greatest {m} {n} c∣m c∣n with ≤-split m n
... | inl  m<n      = gcd′-greatest (Wf-< n) m<n c∣n c∣m 
... | inr (inl n<m) = gcd′-greatest (Wf-< m) n<m c∣m c∣n
... | inr (inr e)   = c∣m

gcd-comm : ∀ m n → gcd m n ＝ gcd n m
gcd-comm m n =
  ∣-antisym (gcd m n) (gcd n m)
    (gcd-greatest (gcd[m,n]∣n m n) (gcd[m,n]∣m m n))
    (gcd-greatest (gcd[m,n]∣n n m) (gcd[m,n]∣m n m))
