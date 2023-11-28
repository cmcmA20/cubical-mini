{-# OPTIONS --safe #-}
module Data.Tree.Binary.Operations where

open import Foundations.Base

open import Meta.Literals.FromProduct

open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Tree.Binary.Base

private variable
  ℓ : Level
  A : Type ℓ

tree→list : Tree A → List A
tree→list  empty     = []
tree→list (leaf x)   = [ x ]
tree→list (node l r) = tree→list l ++ tree→list r

list→tree : List A → Tree A
list→tree []      = empty
list→tree (x ∷ l) = node (leaf x) (list→tree l)

list→tree→list : (l : List A) → tree→list (list→tree l) ＝ l
list→tree→list []       = refl
list→tree→list (x ∷ xs) = ap (x ∷_) (list→tree→list xs)
