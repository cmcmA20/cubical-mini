{-# OPTIONS --safe #-}
module Data.FinSub.Base where

open import Foundations.Base
open import Foundations.Sigma

open import Correspondences.Erased

import Data.Empty.Base as ⊥
open import Data.Nat.Base
  using (ℕ; zero; suc)
open import Data.Nat.Order.Computational

private variable
  ℓ ℓ′ : Level
  @0 m n : ℕ

opaque
  unfolding _≤_
  Fin : @0 ℕ → Type
  Fin n = Σ[ k ꞉ ℕ ] ∥ k < n ∥ᴱ

  fin-β : Fin n → Σ[ k ꞉ ℕ ] ∥ k < n ∥ᴱ
  fin-β = id

  fin-η : Σ[ k ꞉ ℕ ] ∥ k < n ∥ᴱ → Fin n
  fin-η = id

  index : Fin n → ℕ
  index = fst

  bound : (k : Fin n) → ∥ index k < n ∥ᴱ
  bound = snd

  fzero : Fin (suc n)
  fzero = 0 , ∣ tt ∣ᴱ

  fsuc : Fin n → Fin (suc n)
  fsuc (k , ∣ p ∣ᴱ) = suc k , ∣ p ∣ᴱ

  fin-ext : {k₁ k₂ : Fin n} → index k₁ ＝ index k₂ → k₁ ＝ k₂
  fin-ext {n} = Σ-prop-path $ λ z → ∥-∥ᴱ-is-prop (≤-is-prop {m = suc z} {n = n})

  -- TODO feels clunky, how to improve it?
  -- elim
  --   : (P : ∀ {n} → Fin n → Type ℓ)
  --   → (∀ {n} → P {suc n} fzero)
  --   → (∀ {n} {fn : Fin n} → P fn → P (fsuc fn))
  --   → {n : ℕ} (fn : Fin n) → P fn
  -- elim P fz fs {0} (_ , ∣ p ∣ᴱ) = ⊥.absurd (¬sucn≤0 {n = 0} p)
  -- elim P fz fs {suc n} (0 , _) = fz
  -- elim P fz fs {suc n} (suc k , ∣ p ∣ᴱ) = fs $ elim P fz fs $ k , ∣ p ∣ᴱ
