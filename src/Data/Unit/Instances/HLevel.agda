{-# OPTIONS --safe #-}
module Data.Unit.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.List.Base
open import Data.Unit.Base

instance
  decomp-hlevel-⊤ : goal-decomposition (quote is-of-hlevel) ⊤
  decomp-hlevel-⊤ = decomp (quote ⊤-is-of-hlevel) (`level-same ∷ [])
