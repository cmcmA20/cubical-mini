{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Finite where

open import Meta.Prelude

open import Meta.Effect.Bind

open import Correspondences.Finite.Bishop
open import Correspondences.Finite.ManifestBishop

open import Data.Maybe.Properties
open import Data.Fin.Computational.Closure
open import Data.Sum.Properties
open import Data.Unit.Instances.Finite

open import Truncation.Propositional.Instances.Bind

private variable
  ℓ : Level
  A : Type ℓ

instance
  maybe-manifest-bishop-finite
    : ⦃ A-mbf : Manifest-bishop-finite A ⦄ → Manifest-bishop-finite (Maybe A)
  maybe-manifest-bishop-finite = fin $
    maybe-as-sum ∙ ⊎-ap (enumeration auto) (enumeration auto) ∙ fin-coproduct

  maybe-is-bishop-finite
    : ⦃ A-bf : is-bishop-finite A ⦄
    → is-bishop-finite (Maybe A)
  maybe-is-bishop-finite ⦃ A-bf ⦄ = fin₁ do
    aeq ← enumeration₁ A-bf
    ueq ← enumeration₁ manifest-bishop-finite→is-bishop-finite
    pure $ maybe-as-sum ∙ ⊎-ap ueq aeq ∙ fin-coproduct
