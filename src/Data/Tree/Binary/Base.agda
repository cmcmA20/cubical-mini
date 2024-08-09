{-# OPTIONS --safe #-}
module Data.Tree.Binary.Base where

open import Foundations.Base

open import Data.Bool.Base using (Bool; false; true)

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
  : {A : 𝒰 ℓ} {P : Tree A → 𝒰 ℓ′}
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

is-empty? is-leaf? is-node? : Tree A → Bool
is-empty? empty = true
is-empty? (leaf _) = false
is-empty? (node _ _) = false

is-leaf? empty = false
is-leaf? (leaf _) = true
is-leaf? (node _ _) = false

is-node? empty = false
is-node? (leaf -) = false
is-node? (node _ _) = true
