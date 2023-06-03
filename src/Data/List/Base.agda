{-# OPTIONS --safe #-}
module Data.List.Base where

open import Foundations.Base

open import Agda.Builtin.List public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

head : A → List A → A
head def []      = def
head _   (x ∷ _) = x

tail : List A → List A
tail []       = []
tail (_ ∷ xs) = xs

elim
  : (P : List A → Type ℓ′)
  → P []
  → (∀ x xs → P xs → P (x ∷ xs))
  → ∀ xs → P xs
elim P p[] p∷ []       = p[]
elim P p[] p∷ (x ∷ xs) = p∷ x xs (elim P p[] p∷ xs)

fold-r : (A → B → B) → B → List A → B
fold-r f x = elim _ x (λ x _ → f x)

fold-l : (B → A → B) → B → List A → B
fold-l f x []       = x
fold-l f x (a ∷ as) = fold-l f (f x a) as

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

infixr 5 _++_
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ x ∷ []

reverse-fast : List A → List A
reverse-fast = fold-l (flip _∷_) []
