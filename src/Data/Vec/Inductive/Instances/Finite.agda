{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Groupoid
open import Meta.Search.Finite.Bishop
open import Meta.Search.Finite.ManifestBishop

open import Data.Vec.Inductive.Base
open import Data.Vec.Instances.Finite
  using ()
  renaming ( vec-is-bishop-finite to vec-is-bishop-finiteᵈ
           ; vec-manifest-bishop-finite to vec-manifest-bishop-finiteᵈ)

open import Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

vec-manifest-bishop-finite : Manifest-bishop-finite A → Manifest-bishop-finite (Vec A n)
vec-manifest-bishop-finite = manifest-bishop-finite-≃ (default≃inductive ⁻¹) ∘ vec-manifest-bishop-finiteᵈ

vec-is-bishop-finite : is-bishop-finite A → is-bishop-finite (Vec A n)
vec-is-bishop-finite = is-bishop-finite-≃ (default≃inductive ⁻¹) ∘ vec-is-bishop-finiteᵈ

instance
  decomp-fin-vec : goal-decomposition (quote Manifest-bishop-finite) (Vec A n)
  decomp-fin-vec = decomp (quote vec-manifest-bishop-finite) [ `search (quote Manifest-bishop-finite) ]

  decomp-fin₁-vec : goal-decomposition (quote is-bishop-finite) (Vec A n)
  decomp-fin₁-vec = decomp (quote vec-is-bishop-finite) [ `search (quote is-bishop-finite) ]
