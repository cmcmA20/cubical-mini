{-# OPTIONS --safe #-}
module Data.Maybe.Instances.HLevel where

open import Foundations.Base

open import Meta.Reflection.HLevel

open import Data.List.Base

open import Data.Maybe.Path public

instance
  hlevel-decomp-Maybe
    : ∀ {ℓ} {A : Type ℓ}
    → hlevel-decomposition (Maybe A)
  hlevel-decomp-Maybe = decomp (quote maybe-is-of-hlevel)
    (`level-minus 2 ∷ `search ∷ [])
