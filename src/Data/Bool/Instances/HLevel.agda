{-# OPTIONS --safe #-}
module Data.Bool.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.Bool.Path
open import Data.List.Base

instance
  decomp-hlevel-bool : goal-decomposition (quote is-of-hlevel) Bool
  decomp-hlevel-bool = decomp (quote bool-is-of-hlevel) (`level-minus 2 ∷ [])
