{-# OPTIONS --safe #-}
open import Foundations.Base
open import Data.Fin.Interface
open import Data.Nat.Base using (ℕ; zero; suc)

module Data.Tensor.Base {F : @0 ℕ → Type} (fin-impl : FinI F) where

open import Data.HVec.Base

Tensor : ∀{ℓ} {nd} → Vec′ ℕ nd → Type ℓ → Type ℓ
Tensor {nd = 0} _ A = A
Tensor {nd = 1} n A = F n → A
Tensor {nd = suc (suc nd)} (n , ds) A = F n → Tensor ds A
