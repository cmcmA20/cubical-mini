{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.Vec.Inductive.Base
open import Data.Vec.Instances.Finite
  using ()
  renaming (vec-is-bishop-finite to vec-is-bishop-finiteᵈ)

open import Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

vec-is-bishop-finite : is-bishop-finite A → is-bishop-finite (Vec A n)
vec-is-bishop-finite = is-bishop-finite-≃ (default≃inductive ₑ⁻¹) ∘ vec-is-bishop-finiteᵈ

instance
  decomp-fin-vec : goal-decomposition (quote is-bishop-finite) (Vec A n)
  decomp-fin-vec = decomp (quote vec-is-bishop-finite) [ `search (quote is-bishop-finite) ]
