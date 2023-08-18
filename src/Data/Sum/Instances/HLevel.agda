{-# OPTIONS --safe #-}
module Data.Sum.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.Sum.Path public

instance
  decomp-hlevel-⊎
    : ∀ {a b} {A : Type a} {B : Type b}
    → goal-decomposition (quote is-of-hlevel) (A ⊎ B)
  decomp-hlevel-⊎ = decomp (quote ⊎-is-of-hlevel)
    (`level-minus 2 ∷ `search (quote is-of-hlevel) ∷ `search (quote is-of-hlevel) ∷ [])
