{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Finite where

open import Meta.Prelude

open import Combinatorics.Finiteness.Bishop
open import Combinatorics.Finiteness.ManifestBishop

open import Data.Truncation.Propositional.Base
open import Data.Vec.Inductive.Base
open import Data.Vec.Instances.Finite
  using ()
  renaming ( vec-is-bishop-finite to vec-is-bishop-finiteᵈ
           ; vec-manifest-bishop-finite to vec-manifest-bishop-finiteᵈ)

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ

instance
  vec-manifest-bishop-finite : ⦃ A-mbf : Manifest-bishop-finite A ⦄ → Manifest-bishop-finite (Vec A n)
  vec-manifest-bishop-finite = ≃→manifest-bishop-finite (default≃inductive ⁻¹) vec-manifest-bishop-finiteᵈ
  {-# OVERLAPPING vec-manifest-bishop-finite #-}

  vec-is-bishop-finite : ⦃ is-bishop-finite A }} → is-bishop-finite (Vec A n)
  vec-is-bishop-finite = ≃→is-bishop-finite (default≃inductive ⁻¹) vec-is-bishop-finiteᵈ
  {-# OVERLAPPING vec-is-bishop-finite #-}
