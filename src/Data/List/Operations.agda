{-# OPTIONS --safe #-}
-- TODO naming is garbage
module Data.List.Operations where

open import Foundations.Base
open import Data.Bool.Base
open import Data.Nat.Base

open import Data.List.Base

private variable
  ℓ : Level
  A : Type ℓ

all=? : (A → A → Bool) → List A → List A → Bool
all=? eq=? [] [] = true
all=? eq=? [] (x ∷ ys) = false
all=? eq=? (x ∷ xs) [] = false
all=? eq=? (x ∷ xs) (y ∷ ys) = (eq=? x y) and (all=? eq=? xs ys)

length : List A → ℕ
length []       = 0
length (_ ∷ xs) = suc (length xs)
