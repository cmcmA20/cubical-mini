{-# OPTIONS --safe #-}
module Data.Vec.Instances.Finite where

open import Foundations.Base

open import Combinatorics.Finiteness.Bishop
open import Combinatorics.Finiteness.ManifestBishop

open import Data.Nat.Base
open import Data.Unit.Instances.Finite

open import Data.Vec.Base public

private variable
  ℓ ℓ′ : Level
  n : ℕ
  A : Type ℓ
  B : Type ℓ′

-- NB: vector definition is transparent, so these instances won't ever
-- be selected by instance search, they are used to easily transfer finiteness
-- between different vector implementations

instance
  vec-manifest-bishop-finite : ⦃ A-mbf : Manifest-bishop-finite A ⦄ → Manifest-bishop-finite (Vec A n)
  vec-manifest-bishop-finite {A} {0} ⦃ A-mbf ⦄ = lift-manifest-bishop-finite
  vec-manifest-bishop-finite {A} {suc _} ⦃ A-mbf ⦄ =
    ×-manifest-bishop-finite ⦃ A-mbf ⦄ ⦃ vec-manifest-bishop-finite ⦄

  vec-is-bishop-finite : ⦃ A-bf : is-bishop-finite A ⦄ → is-bishop-finite (Vec A n)
  vec-is-bishop-finite {A} {0} ⦃ A-bf ⦄ = lift-is-bishop-finite
  vec-is-bishop-finite {A} {suc _} ⦃ A-bf ⦄ =
    ×-is-bishop-finite ⦃ A-bf ⦄ ⦃ vec-is-bishop-finite ⦄
