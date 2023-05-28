{-# OPTIONS --safe #-}
module Data.Vec.Base where

open import Foundations.Base
open import Data.Nat.Base
  using (ℕ; zero; suc)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  n : ℕ

infixr 5 _∷_
data Vec (A : Type ℓ) : @0 ℕ → Type ℓ where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

elim
  : (P : ∀ {@0 n} → Vec A n → Type ℓ′)
  → P []
  → (∀ {n} x (xs : Vec A n) → P xs → P (x ∷ xs))
  → ∀ {n} (xs : Vec A n) → P xs
elim P p[] p∷ [] = p[]
elim P p[] p∷ (x ∷ xs) = p∷ x xs (elim P p[] p∷ xs)

map : (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs
