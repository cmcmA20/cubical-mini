{-# OPTIONS --safe #-}
module Data.Nat.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.Nat.Path

instance
  decomp-hlevel-ℕ : goal-decomposition (quote is-of-hlevel) ℕ
  decomp-hlevel-ℕ = decomp (quote ℕ-is-of-hlevel) (`level-minus 2 ∷ [])
