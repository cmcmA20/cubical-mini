{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Effect.Bind
open import Meta.Search.Finite.Bishop
open import Meta.Search.Finite.ManifestBishop

open import Data.Maybe.Properties
open import Data.Fin.Computational.Closure
open import Data.Sum.Properties
open import Data.Unit.Instances.Finite

open import Truncation.Propositional.Instances.Bind

private variable
  ℓ : Level
  A : Type ℓ

maybe-manifest-bishop-finite : Manifest-bishop-finite A → Manifest-bishop-finite (Maybe A)
maybe-manifest-bishop-finite fi = fin $
  maybe-as-sum ∙ₑ ⊎-ap (enumeration by-instance) (enumeration fi) ∙ₑ fin-coproduct

maybe-is-bishop-finite : is-bishop-finite A → is-bishop-finite (Maybe A)
maybe-is-bishop-finite fi = fin₁ do
  aeq ← enumeration₁ fi
  ueq ← enumeration₁ bishop-finite!
  pure $ maybe-as-sum ∙ₑ ⊎-ap ueq aeq ∙ₑ fin-coproduct

instance
  decomp-fin-maybe : goal-decomposition (quote Manifest-bishop-finite) (Maybe A)
  decomp-fin-maybe = decomp (quote maybe-manifest-bishop-finite) [ `search (quote Manifest-bishop-finite) ]

  decomp-fin₁-maybe : goal-decomposition (quote is-bishop-finite) (Maybe A)
  decomp-fin₁-maybe = decomp (quote maybe-is-bishop-finite) [ `search (quote is-bishop-finite) ]
