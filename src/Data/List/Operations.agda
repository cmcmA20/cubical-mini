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

replicate : ℕ → A → List A
replicate 0 _       = []
replicate (suc n) e = e ∷ replicate n e

filter : (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
filter p (x ∷ xs)    | true  = x ∷ filter p xs
filter p (x ∷ xs)    | false = filter p xs

drop : ℕ → List A → List A
drop 0 = id
drop (suc n) (x ∷ xs) = drop n xs
drop _ _ = []

take : ℕ → List A → List A
take 0 _ = []
take (suc n) (x ∷ xs) = x ∷ take n xs
take _ _ = []
