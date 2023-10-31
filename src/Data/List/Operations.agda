{-# OPTIONS --safe #-}
-- TODO naming is garbage
module Data.List.Operations where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Maybe.Base
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

elem : (A → A → Bool) → A → List A → Bool
elem _    t []       = false
elem eq=? t (x ∷ xs) = eq=? t x or elem eq=? t xs

-- O(n²)
nub-slow : (A → A → Bool) → List A → List A
nub-slow {A} eq=? = nub′ [] where
  nub′ : List A → List A → List A
  nub′ _ [] = []
  nub′ acc (x ∷ xs) =
    if elem eq=? x acc
      then nub′ acc xs
      else x ∷ nub′ (x ∷ acc) xs

nub-unsafe : (A → A → Bool) → List A → List A
nub-unsafe _ [] = []
nub-unsafe _ (x ∷ []) = x ∷ []
nub-unsafe eq=? (x ∷ y ∷ xs) =
  if eq=? x y
    then id
    else x ∷_
  $ nub-unsafe eq=? (y ∷ xs)

insert : (A → A → Bool) → A → List A → List A
insert _ x [] = x ∷ []
insert le? x (a ∷ as) =
  if le? x a
    then x ∷ a ∷ as
    else a ∷ insert le? x as

insertion-sort : (A → A → Bool) → List A → List A
insertion-sort _ [] = []
insertion-sort le? (x ∷ xs) = insert le? x $ insertion-sort le? xs

lookup : (A → A → Bool) → A → List A → Maybe ℕ
lookup {A} eq=? t = go 0 where
  go : ℕ → List A → Maybe ℕ
  go _ [] = nothing
  go ix (x ∷ xs) =
    if eq=? t x then just ix else go (suc ix) xs
