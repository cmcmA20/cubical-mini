{-# OPTIONS --safe #-}
module Data.Maybe.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.List.Base

open import Data.Maybe.Path public

instance
  hlevel-decomp-Maybe
    : ∀ {ℓ} {A : Type ℓ}
    → goal-decomposition (quote is-of-hlevel) (Maybe A)
  hlevel-decomp-Maybe = decomp (quote maybe-is-of-hlevel)
    (`level-minus 2 ∷ `search (quote is-of-hlevel) ∷ [])
