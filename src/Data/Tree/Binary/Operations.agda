{-# OPTIONS --safe #-}
module Data.Tree.Binary.Operations where

open import Foundations.Base
open import Data.Tree.Binary.Base
open import Data.List

private variable
  ℓ : Level
  A : 𝒰 ℓ

to-list : Tree A → List A
to-list  empty     = []
to-list (leaf x)   = x ∷ []
to-list (node l r) = to-list l ++ to-list r

from-list : List A → Tree A
from-list []      = empty
from-list (x ∷ l) = node (leaf x) (from-list l)

to-from : (l : List A) → to-list (from-list l) ＝ l
to-from []      = refl
to-from (x ∷ l) = ap (x ∷_) (to-from l)
