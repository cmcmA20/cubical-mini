{-# OPTIONS --safe #-}
module Data.Dec.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.List.Base

open import Data.Dec.Path

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  decomp-hlevel-dec : goal-decomposition (quote is-of-hlevel) (Dec A)
  decomp-hlevel-dec = decomp (quote dec-is-of-hlevel) (`level-same ∷ `search (quote is-of-hlevel) ∷ [])
