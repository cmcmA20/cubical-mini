{-# OPTIONS --safe #-}
module Cubical.HITs.Int.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)

open import Cubical.Instances.HLevels

data ℤ : Type₀ where
  neg  : ℕ → ℤ
  pos  : ℕ → ℤ
  0₋≡0₊ : neg 0 ≡ pos 0

∣_∣ : ℤ → ℕ
∣ neg n ∣ = n
∣ pos n ∣ = n
∣ 0₋≡0₊ _ ∣ = zero

negate : ℤ → ℤ
negate (neg n) = pos n
negate (pos n) = neg n
negate (0₋≡0₊ i) = sym 0₋≡0₊ i

succ : ℤ → ℤ
succ (neg zero)    = pos 1
succ (neg (suc n)) = neg n
succ (pos  n)      = pos (suc n)
succ (0₋≡0₊ _) = pos 1

pred : ℤ → ℤ
pred (neg n)       = neg (suc n)
pred (pos zero)    = neg 1
pred (pos (suc n)) = pos n
pred (0₋≡0₊ _) = neg 1

module _ {ℓ : Level} {B : ℤ → Type ℓ}
         (neg* : (n : ℕ) → B (neg n))
         (pos* : (n : ℕ) → B (pos n))
         (seg* : PathP (λ i → B (0₋≡0₊ i)) (neg* 0) (pos* 0)) where
  elim : (m : ℤ) → B m
  elim (neg n) = neg* n
  elim (pos n) = pos* n
  elim (0₋≡0₊ i) = seg* i

module _ {ℓ : Level} {B : ℤ → Type ℓ}
         (neg* : (n : ℕ) → B (neg n))
         (pos* : (n : ℕ) → B (pos n))
         ⦃ B-prop : {m : ℤ} → IsProp (B m) ⦄ where
  elim-prop : (m : ℤ) → B m
  elim-prop = elim neg* pos* (toPathP (B-prop .iohl _ _))
