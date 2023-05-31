{-# OPTIONS --safe #-}
module Data.List.Instances.HLevel where

open import Foundations.Base
open import Data.List.Base
open import Meta.Reflection.HLevel

open import Data.List.Path public

instance
  hlevel-decomp-List
    : ∀ {ℓ} {A : Type ℓ}
    → hlevel-decomposition (List A)
  hlevel-decomp-List = decomp (quote list-is-of-hlevel)
    (`level-minus 2 ∷ `search ∷ [])
