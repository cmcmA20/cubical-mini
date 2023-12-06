{-# OPTIONS --safe #-}
open import Foundations.Base
open import Data.Fin.Interface
open import Data.Nat.Base using (ℕ; zero; suc)

module Data.Tensor.Base {F : @0 ℕ → Type} (fin-impl : FinI F) where

open import Data.Vec.Inductive.Base

Tensor : ∀{ℓ} {@0 nd} (ds : Vec ℕ nd) → Type ℓ → Type ℓ
Tensor []       A = A
Tensor (n ∷ ds) A = F n → Tensor ds A
