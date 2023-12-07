{-# OPTIONS --safe #-}
module Data.Vec.Instances.Finite where

open import Foundations.Base

open import Meta.Search.Finite.Bishop
open import Meta.Search.Finite.ManifestBishop

open import Data.Nat.Base
open import Data.Unit.Instances.Finite

open import Data.Vec.Base public

private variable
  ℓ ℓ′ : Level
  n : ℕ
  A : Type ℓ
  B : Type ℓ′

vec-manifest-bishop-finite : Manifest-bishop-finite A → Manifest-bishop-finite (Vec A n)
vec-manifest-bishop-finite {A} {0} _ = manifest-bishop-finite!
vec-manifest-bishop-finite {A} {suc _} A-fin =
  ×-manifest-bishop-finite A-fin (vec-manifest-bishop-finite A-fin)

vec-is-bishop-finite : is-bishop-finite A → is-bishop-finite (Vec A n)
vec-is-bishop-finite {A} {0} _ = bishop-finite!
vec-is-bishop-finite {A} {suc _} A-fin =
  ×-is-bishop-finite A-fin (vec-is-bishop-finite A-fin)

instance
  decomp-fin-vec : goal-decomposition (quote Manifest-bishop-finite) (Vec A n)
  decomp-fin-vec = decomp (quote vec-manifest-bishop-finite) [ `search (quote Manifest-bishop-finite) ]

  decomp-fin₁-vec : goal-decomposition (quote is-bishop-finite) (Vec A n)
  decomp-fin₁-vec = decomp (quote vec-is-bishop-finite) [ `search (quote is-bishop-finite) ]
