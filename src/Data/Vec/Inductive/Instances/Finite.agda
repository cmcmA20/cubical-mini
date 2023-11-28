{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.Vec.Inductive.Base
open import Data.Vec.Instances.Finite
  using ()
  renaming (vec-is-fin-set to vec-is-fin-setᵈ)

open import Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

vec-is-fin-set : is-fin-set A → is-fin-set (Vec A n)
vec-is-fin-set = is-fin-set-≃ (default≃inductive ₑ⁻¹) ∘ vec-is-fin-setᵈ

instance
  decomp-fin-vec : goal-decomposition (quote is-fin-set) (Vec A n)
  decomp-fin-vec = decomp (quote vec-is-fin-set) [ `search (quote is-fin-set) ]
