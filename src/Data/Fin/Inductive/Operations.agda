{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Operations where

open import Foundations.Base

open import Data.Empty.Base as ⊥
  using (_≠_)
open import Data.Fin.Interface
open import Data.Reflects.Base
open import Data.Maybe.Base
  using (Maybe; nothing; just)
open import Data.Nat.Base
  using (ℕ; zero; suc)
open import Data.Nat.Order.Base
open import Data.Sum.Base
  using (_⊎ₜ_; inl; inr)
open import Data.Fin.Inductive.Base

private variable
  ℓ : Level
  A : Type ℓ
  m n : ℕ

ℕ→fin : (m : ℕ) → m < n → Fin n
ℕ→fin {n = zero}    m     m<n = false! m<n
ℕ→fin {n = suc n}  zero   m<n = fzero
ℕ→fin {n = suc n} (suc m) m<n = fsuc (ℕ→fin m (<-peel m<n))

fmax : Fin (suc n)
fmax {n = zero}  = fzero
fmax {n = suc n} = fsuc fmax

fmax0 : 0 < n → Fin n
fmax0 {n = zero}  z<n = false! z<n
fmax0 {n = suc n} z<n = fmax
