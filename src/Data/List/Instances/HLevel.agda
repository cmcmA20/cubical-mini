{-# OPTIONS --safe #-}
module Data.List.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.List.Base
open import Data.List.Path public

instance
  decomp-hlevel-list
    : ∀ {ℓ} {A : Type ℓ}
    → goal-decomposition (quote is-of-hlevel) (List A)
  decomp-hlevel-list = decomp (quote list-is-of-hlevel)
    (`level-minus 2 ∷ `search (quote is-of-hlevel) ∷ [])
