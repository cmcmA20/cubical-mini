{-# OPTIONS --safe #-}
-- TODO naming is garbage
module Data.List.Operations where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Nat.Base

open import Data.List.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A       : Type ℓ
  B       : Type ℓ′
  C       : Type ℓ″

all=? : (A → A → Bool) → List A → List A → Bool
all=? eq=? [] [] = true
all=? eq=? [] (x ∷ ys) = false
all=? eq=? (x ∷ xs) [] = false
all=? eq=? (x ∷ xs) (y ∷ ys) = (eq=? x y) and (all=? eq=? xs ys)

length : List A → ℕ
length []       = 0
length (_ ∷ xs) = suc (length xs)

filter : (A → Bool) → List A → List A
filter pred = fold-r (λ x xs → if pred x then x ∷ xs else xs) []

any : (A → Bool) → List A → Bool
any pred []       = false
any pred (x ∷ xs) = if pred x then true else any pred xs

all : (A → Bool) → List A → Bool
all pred []       = true
all pred (x ∷ xs) = if pred x then all pred xs else false

null : List A → Bool
null [] = true
null _  = false

scan-r : (f : A → B → C × B) (z : B) (xs : List A) → List C × B
scan-r f z [] = [] , z
scan-r f z (x ∷ xs) with scan-r f z xs
... | trace , res
  with f x res
... | c , res
  = c ∷ trace , res