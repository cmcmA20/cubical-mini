{-# OPTIONS --safe #-}
module Data.Sum.Instances.Finite where

open import Meta.Prelude

open import Meta.Effect.Bind

open import Combinatorics.Finiteness.Bishop
open import Combinatorics.Finiteness.ManifestBishop

open import Data.Fin.Computational.Closure
open import Data.Sum.Properties
open import Data.Truncation.Propositional.Instances.Bind

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

instance
  ⊎-manifest-bishop-finite
    : ⦃ A-mbf : Manifest-bishop-finite A ⦄ → ⦃ B-mbf : Manifest-bishop-finite B ⦄
    → Manifest-bishop-finite (A ⊎ B)
  ⊎-manifest-bishop-finite = fin $ ⊎-ap (enumeration auto) (enumeration auto) ∙ fin-coproduct
  {-# OVERLAPPING ⊎-manifest-bishop-finite #-}

  ⊎-is-bishop-finite
    : ⦃ A-bf : is-bishop-finite A ⦄ → ⦃ B-bf : is-bishop-finite B ⦄
    → is-bishop-finite (A ⊎ B)
  ⊎-is-bishop-finite = fin₁ do
    aeq ← enumeration₁ auto
    beq ← enumeration₁ auto
    pure $ ⊎-ap aeq beq ∙ fin-coproduct
  {-# OVERLAPPING ⊎-is-bishop-finite #-}
