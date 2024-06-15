{-# OPTIONS --safe --no-exact-split #-}
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

-- aka fold-r
rec : B → (A → B → B) → List A → B
rec x _ []       = x
rec x f (a ∷ as) = f a (rec x f as)

fold-l : (B → A → B) → B → List A → B
fold-l f x []       = x
fold-l f x (a ∷ as) = fold-l f (f x a) as

infixr 5 _++_
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : List (List A) → List A
concat = rec [] (_++_)

reverse : List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ x ∷ []

reverse-fast : List A → List A
reverse-fast = fold-l (flip _∷_) []

intersperse : A -> List A -> List A
intersperse _ []       = []
intersperse _ (x ∷ []) = x ∷ []
intersperse s (x ∷ xs) = x ∷ s ∷ intersperse s xs

intercalate : (x : A) (xs : List A) → List A
intercalate x []           = []
intercalate x (y ∷ [])     = y ∷ []
intercalate x (y ∷ z ∷ xs) = y ∷ x ∷ intercalate x (z ∷ xs)
