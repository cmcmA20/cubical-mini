{-# OPTIONS --safe #-}
module Data.Vec.Operations where

open import Foundations.Base

open import Data.Fin.Base
open import Data.Vec.Base public

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

tabulate : (Fin n → A) → Vec A n
tabulate {n = 0}     _ = []
tabulate {n = suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

lookup : Vec A n → Fin n → A
lookup {n = suc _} (x ∷ _)  fzero    = x
lookup {n = suc _} (_ ∷ xs) (fsuc k) = lookup xs k
