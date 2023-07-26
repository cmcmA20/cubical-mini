{-# OPTIONS --safe #-}
module Data.Tree.Binary.Base where

open import Foundations.Base

data Tree {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  empty : Tree A
  leaf  : A → Tree A
  node  : Tree A → Tree A → Tree A

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  tl tr : Tree A

elim
  : {P : Tree A → 𝒰 ℓ′}
    (empty* : P empty)
    (leaf* : Π[ x ꞉ A ] P (leaf x))
    (node* : {tl tr : Tree A} → P tl → P tr → P (node tl tr))
  → Π[ t ꞉ Tree A ] P t
elim empty* _ _ empty = empty*
elim _ leaf* _ (leaf x) = leaf* x
elim empty* leaf* node* (node tl tr) =
  node* (elim empty* leaf* (λ {tl′} → node* {tl′}) tl)
        (elim empty* leaf* (λ {tl′} → node* {tl′}) tr)

rec : (empty* : B)
      (leaf* : Π[ x ꞉ A ] B)
      (node* : B → B → B)
    → Π[ t ꞉ Tree A ] B
rec empty* leaf* node* = elim empty* leaf* node*

map : (A → B) → Tree A → Tree B
map _ empty = empty
map f (leaf x) = leaf (f x)
map f (node l r) = node (map f l) (map f r)
