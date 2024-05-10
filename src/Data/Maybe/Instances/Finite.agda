{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Finite where

open import Meta.Prelude

open import Meta.Effect.Bind

open import Combinatorics.Finiteness.Bishop
open import Combinatorics.Finiteness.ManifestBishop

open import Data.Maybe.Properties
open import Data.Fin.Computational.Closure
open import Data.Sum.Properties
open import Data.Truncation.Propositional.Instances.Bind
open import Data.Unit.Instances.Finite

private variable
  ℓ : Level
  A : Type ℓ

instance
  maybe-manifest-bishop-finite
    : ⦃ A-mbf : Manifest-bishop-finite A ⦄ → Manifest-bishop-finite (Maybe A)
  maybe-manifest-bishop-finite = fin $
    maybe-as-sum ∙ ⊎-ap (enumeration auto) (enumeration auto) ∙ fin-coproduct
  {-# OVERLAPPING maybe-manifest-bishop-finite #-}

  maybe-is-bishop-finite
    : ⦃ A-bf : is-bishop-finite A ⦄
    → is-bishop-finite (Maybe A)
  maybe-is-bishop-finite ⦃ A-bf ⦄ = fin₁ do
    aeq ← enumeration₁ A-bf
    ueq ← enumeration₁ manifest-bishop-finite→is-bishop-finite
    pure $ maybe-as-sum ∙ ⊎-ap ueq aeq ∙ fin-coproduct
  {-# OVERLAPPING maybe-is-bishop-finite #-}
