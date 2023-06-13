{-# OPTIONS --safe #-}
module Data.Sum.Instances.HLevel where

open import Foundations.Base

open import Meta.HLevel

open import Data.List.Base

open import Data.Sum.Path public

instance
  hlevel-decomp-⊎
    : ∀ {a b} {A : Type a} {B : Type b}
    → hlevel-decomposition (A ⊎ B)
  hlevel-decomp-⊎ = decomp (quote ⊎-is-of-hlevel)
    (`level-minus 2 ∷ `search ∷ `search ∷ [])
