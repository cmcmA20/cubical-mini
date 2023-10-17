{-# OPTIONS --safe #-}
module Data.Vec.Base where

open import Foundations.Base

open import Data.Nat.Base public
  using (ℕ; zero; suc; _+_)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  @0 m n : ℕ

infixr 5 _∷_
data Vec (A : Type ℓ) : @0 ℕ → Type ℓ where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

elim
  : (P : ∀ {@0 n} → Vec A n → Type ℓ′)
  → P []
  → (∀ {@0 n} x (xs : Vec A n) → P xs → P (x ∷ xs))
  → ∀ {@0 n} (xs : Vec A n) → P xs
elim P p[] p∷ [] = p[]
elim P p[] p∷ (x ∷ xs) = p∷ x xs (elim P p[] p∷ xs)

rec
  : {B : @0 ℕ → Type ℓ′}
  → B 0
  → (∀ {@0 n} (x : A) → B n → B (suc n))
  → ∀ {@0 n} (xs : Vec A n) → B n
rec {B} b[] b∷ = elim (λ {n} _ → B n) b[] (λ x _ → b∷ x)

map : (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : (n : ℕ) → A → Vec A n
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

_++_ : Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

head : Vec A (suc n) → A
head (x ∷ _) = x

tail : Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs
