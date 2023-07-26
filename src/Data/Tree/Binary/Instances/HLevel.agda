{-# OPTIONS --safe #-}
module Data.Tree.Binary.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.List.Base
open import Data.Tree.Binary.Base
open import Data.Tree.Binary.Path public

instance
  decomp-hlevel-binary-tree
    : ∀ {ℓ} {A : Type ℓ}
    → goal-decomposition (quote is-of-hlevel) (Tree A)
  decomp-hlevel-binary-tree = decomp (quote tree-is-of-hlevel)
    (`level-minus 2 ∷ `search (quote is-of-hlevel) ∷ [])
