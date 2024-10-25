{-# OPTIONS --safe #-}
module Data.Nat.Order.Inductive.Decidability where

open import Meta.Prelude
open Variadics _

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Nat.Order.Inductive.Base
open import Data.Reflects.Base as R
open import Data.Sum.Base

private variable m n k : ℕ

instance
  Reflects-ℕ-≤ : {m n : ℕ} → Reflects (m ≤ n) (m ≤? n)
  Reflects-ℕ-≤ {0}     {_}      = ofʸ z≤
  Reflects-ℕ-≤ {suc _} {0}      = ofⁿ λ ()
  Reflects-ℕ-≤ {suc m} {suc n} with m ≤? n | recall (m ≤?_) n
  ... | false | ⟪ p ⟫ = ofⁿ λ where
    (s≤s m≤n) → so→false! (subst So (ap not p ⁻¹) oh) m≤n
  ... | true  | ⟪ p ⟫ = ofʸ (s≤s (so→true! (subst So (sym p) oh)))

  Dec-≤ : {m n : ℕ} → Dec (m ≤ n)
  Dec-≤ = _ because auto
  {-# OVERLAPPING Dec-≤ #-}

≤-split : Π[ _<_ ⊎ _>_ ⊎ _＝_ ]
≤-split m n with Dec-≤ {suc m} {n}
≤-split m n | yes m<n = inl m<n
≤-split m n | no m≥n with Dec-≤ {suc n} {m}
≤-split m n | no m≥n | yes n<m = inr (inl n<m)
≤-split m n | no m≥n | no n≥m  = inr (inr (go m n m≥n n≥m)) where
  go : ∀ m n → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
  go 0       0       _ _ = refl
  go 0       (suc _) p _ = false! p
  go (suc _) 0       _ q = false! q
  go (suc m) (suc n) p q = ap suc (go m n (p ∘ s≤ʰs) (q ∘ s≤ʰs))
