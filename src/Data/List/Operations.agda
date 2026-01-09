{-# OPTIONS --safe --no-exact-split #-}
-- TODO naming is garbage
module Data.List.Operations where

open import Foundations.Base

open import Meta.Effect.Map
open import Meta.Effect.Idiom

open import Data.Bool.Base
open import Data.Maybe.Base as Maybe
open import Data.Maybe.Instances.Map
open import Data.Nat.Base
open import Data.Nat.Two
open import Data.Fin.Computational.Base as Fin
open import Data.Reflects.Base as Reflects

open import Data.List.Base as List
open import Data.List.Instances.Idiom
open import Data.List.Instances.Map

open Map ⦃ ... ⦄

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  x : A
  xs : List A

empty? : List A → Bool
empty? []      = true
empty? (_ ∷ _) = false

snoc : List A → A → List A
snoc []      y = y ∷ []
snoc (x ∷ l) y = x ∷ snoc l y

_∷r_ = snoc
infixl 20 _∷r_

unsnoc : A → List A → List A × A
unsnoc y []       = [] , y
unsnoc y (x ∷ xs) = first (y ∷_) (unsnoc x xs)

last : A → List A → A
last y = snd ∘ unsnoc y

all : (A → Bool) → List A → Bool
all p = List.rec true _and_ ∘ map p

any : (A → Bool) → List A → Bool
any p = List.rec false _or_ ∘ map p

count : (A → Bool) → List A → ℕ
count p = List.rec 0 (λ x n → bit (p x) + n)

length : List A → ℕ
length []       = 0
length (_ ∷ xs) = suc (length xs)

_!ᵐ_ : List A → ℕ → Maybe A
[]       !ᵐ  _      = nothing
(x ∷ _)  !ᵐ  zero   = just x
(_ ∷ xs) !ᵐ (suc n) = xs !ᵐ n

_!ᶠ_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) !ᶠ mk-fin  zero               = x
(x ∷ xs) !ᶠ mk-fin (suc index) {bound} = xs !ᶠ mk-fin index {bound}

unconsᵐ : List A → Maybe (A × List A)
unconsᵐ []       = nothing
unconsᵐ (x ∷ xs) = just (x , xs)

unsnocᵐ : List A → Maybe (List A × A)
unsnocᵐ []       = nothing
unsnocᵐ (x ∷ xs) = just (unsnoc x xs)

headᵐ : List A → Maybe A
headᵐ = map fst ∘ unconsᵐ

tailᵐ : List A → Maybe (List A)
tailᵐ = map snd ∘ unconsᵐ

replicate : ℕ → A → List A
replicate 0 _       = []
replicate (suc n) e = e ∷ replicate n e

filter : (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

find : (A → Bool) → List A → ℕ
find p []       = 0
find p (x ∷ xs) = if p x then 0 else suc (find p xs)

findᵐ : (A → Bool) → List A → Maybe A
findᵐ p []       = nothing
findᵐ p (x ∷ xs) = if p x then just x else findᵐ p xs

-- slow: O(n²)
nub-acc : (A → A → Bool) → List A → List A → List A
nub-acc _    _   []       = []
nub-acc eq=? acc (x ∷ xs) =
  if any (eq=? x) acc
    then nub-acc eq=? acc xs
    else x ∷ nub-acc eq=? (x ∷ acc) xs

nub : (A → A → Bool) → List A → List A
nub eq=? = nub-acc eq=? []

-- fast, but only removes consecutive duplicates
nub-consec : (A → A → Bool) → List A → List A
nub-consec _ [] = []
nub-consec _ (x ∷ []) = x ∷ []
nub-consec eq=? (x ∷ y ∷ xs) =
  if eq=? x y
    then id
    else x ∷_
  $ nub-consec eq=? (y ∷ xs)

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

take : ℕ → List A → List A
take 0       _        = []
take _       []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ℕ → List A → List A
drop 0       xs       = xs
drop _       []       = []
drop (suc n) (x ∷ xs) = drop n xs

count-from-to : ℕ → ℕ → List ℕ
count-from-to _          0        = []
count-from-to 0          (suc to) = 0 ∷ (suc <$> count-from-to 0 to)
count-from-to (suc from) (suc to) = suc <$> count-from-to from to

map-maybe : (A → Maybe B) → List A → List B
map-maybe f []       = []
map-maybe f (x ∷ xs) =
  Maybe.rec
    (map-maybe f xs)
    (_∷ map-maybe f xs)
    (f x)

map-up : (ℕ → A → B) → ℕ → List A → List B
map-up _ _ []       = []
map-up f n (x ∷ xs) = f n x ∷ map-up f (suc n) xs

take-while : (A → Bool) → List A → List A
take-while p []       = []
take-while p (x ∷ xs) =
  if p x then x ∷ take-while p xs
         else []

drop-while : (A → Bool) → List A → List A
drop-while p []       = []
drop-while p (x ∷ xs) =
  if p x then drop-while p xs
         else x ∷ xs

span : (p : A → Bool) → List A → List A × List A
span p []       = [] , []
span p (x ∷ xs) =
  if p x then first (x ∷_) (span p xs)
         else [] , x ∷ xs

partition : (p : A → Bool) → List A → List A × List A
partition p []       = [] , []
partition p (x ∷ xs) =
  if p x then first (x ∷_) (partition p xs)
         else second (x ∷_) (partition p xs)

split-at : ℕ → List A → List A × List A
split-at 0       xs       = [] , xs
split-at (suc n) []       = [] , []
split-at (suc n) (x ∷ xs) = first (x ∷_) (split-at n xs)

zip-with : (A → B → C) → List A → List B → List C
zip-with f []       []       = []
zip-with f []       (_ ∷ _)  = []
zip-with f (_ ∷ _)  []       = []
zip-with f (x ∷ xs) (y ∷ ys) = f x y ∷ zip-with f xs ys

zip : List A → List B → List (A × B)
zip []       _        = []
zip _        []       = []
zip (a ∷ as) (b ∷ bs) = (a , b) ∷ zip as bs

unzip : List (A × B) → List A × List B
unzip [] = [] , []
unzip ((a , b) ∷ xs) = ((a ∷_) × (b ∷_)) $ unzip xs
