{-# OPTIONS --safe #-}
module Data.Nat.Order.Inductive.Decidability where

open import Meta.Prelude

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Nat.Order.Inductive.Base
open import Data.Reflects.Base as R
open import Data.Sum.Base

private variable m n k : ℕ

instance
  ≤-reflects : {m n : ℕ} → Reflects⁰ (m ≤ n) (m ≤? n)
  ≤-reflects {0}     {_}      = ofʸ z≤
  ≤-reflects {suc _} {0}      = ofⁿ λ ()
  ≤-reflects {suc m} {suc n} with m ≤? n | recall (m ≤?_) n
  ... | false | ⟪ p ⟫ = ofⁿ λ where
    (s≤s m≤n) → so→false! ⦃ ≤-reflects {m} {n} ⦄ (subst So (ap not p ⁻¹) oh) m≤n
  ... | true  | ⟪ p ⟫ = ofʸ (s≤s (so→true! ⦃ ≤-reflects {m} {n} ⦄ (subst So (sym p) oh)))

  Dec-≤ : {m n : ℕ} → Dec (m ≤ n)
  Dec-≤ {m} {n} .does  = m ≤? n
  Dec-≤ {m} {n} .proof = ≤-reflects
  {-# OVERLAPPING Dec-≤ #-}

≤-split : (m n : ℕ) → (m < n) ⊎ (n < m) ⊎ (m ＝ n)
≤-split m n with Dec-≤ {suc m} {n}
≤-split m n | yes m<n = inl m<n
≤-split m n | no m≥n with Dec-≤ {suc n} {m}
≤-split m n | no m≥n | yes n<m = inr (inl n<m)
≤-split m n | no m≥n | no n≥m  = inr (inr (go m n m≥n n≥m)) where
  go : ∀ m n → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
  go 0       0       _ _ = refl
  go 0       (suc _) p _ = absurd $ p (s≤ʰs z≤ʰ)
  go (suc _) 0       _ q = absurd $ q (s≤ʰs z≤ʰ)
  go (suc m) (suc n) p q = ap suc (go m n (p ∘ s≤ʰs) (q ∘ s≤ʰs))
