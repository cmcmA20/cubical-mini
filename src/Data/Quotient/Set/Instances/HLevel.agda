{-# OPTIONS --safe #-}
module Data.Quotient.Set.Instances.HLevel where

open import Foundations.Base

open import Meta.Search.HLevel

open import Data.List.Base

open import Data.Quotient.Set.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  R : A → A → Type ℓ′

instance
  decomp-/₂ : goal-decomposition (quote is-of-hlevel) (A / R)
  decomp-/₂ = decomp (quote /₂-is-of-hlevel) (`level-minus 2 ∷ [])
