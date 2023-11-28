{-# OPTIONS --safe #-}
module Data.Vec.Base where

open import Foundations.Base

open import Data.Nat.Base

Vec : ∀ {ℓ} → Type ℓ → (n : ℕ) → Type ℓ
Vec _ 0             = Lift _ ⊤
Vec A 1             = A
Vec A (suc (suc n)) = A × Vec A (suc n)
