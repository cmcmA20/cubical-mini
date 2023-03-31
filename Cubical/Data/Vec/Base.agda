{- Definition of vectors. Inspired by the Agda Standard Library -}

{-# OPTIONS --safe #-}
module Cubical.Data.Vec.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Fin.Base
open import Cubical.Data.Sigma.Base

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A : Type ℓ
    B : Type ℓ′
    C : Type ℓ″
    m n : ℕ

infixr 5 _∷_

data Vec (A : Type ℓ) : @0 ℕ → Type ℓ where
  []  :                          Vec A zero
  _∷_ : (x : A) (xs : Vec A n) → Vec A (suc n)


-- Basic functions

length : Vec A n → ℕ
length []       = 0
length (x ∷ xs) = suc (length xs)

-- imagine this shit
-- length : ∀ {n} → Vec A n → ℕ
-- length {n = n} _ = n

head : Vec A (suc n) → A
head (x ∷ _) = x

tail : Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

map : (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : A → Vec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

zipWith : (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith {n = zero} _∗_ [] [] = []
zipWith {n = suc n} _∗_ (x ∷ xs) (y ∷ ys) = (x ∗ y) ∷ zipWith _∗_ xs ys

foldr : (A → B → B) → B → Vec A n → B
foldr {n = zero} _∗_ x [] = x
foldr {n = suc n} _∗_ x (y ∷ xs) = y ∗ (foldr _∗_ x xs)

-- Concatenation

infixr 5 _++_

_++_ : Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : Vec (Vec A m) n → Vec A (n · m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

lookup : Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

splitAt : (m : ℕ) {n : ℕ} (xs : Vec A (m + n))
        → Σ[ ys ꞉ Vec A m ] Σ[ zs ꞉ Vec A n ] (xs ≡ ys ++ zs)
splitAt zero    xs       = [] , xs , refl
splitAt (suc m) (x ∷ xs) with splitAt m xs
... | ys , zs , p = x ∷ ys , zs , cong (x ∷_) p

drop : (m : ℕ) {n : ℕ} → Vec A (m + n) → Vec A n
drop m xs = splitAt m xs .snd .fst

take : (m : ℕ) {n : ℕ} → Vec A (m + n) → Vec A m
take m xs = splitAt m xs .fst
