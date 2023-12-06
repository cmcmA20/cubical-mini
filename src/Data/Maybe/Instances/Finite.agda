{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind
open import Meta.Search.Finite.Bishop

open import Data.Maybe.Properties
open import Data.Fin.Computational.Closure
open import Data.Sum.Properties
open import Data.Unit.Instances.Finite

open import Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ

maybe-is-bishop-finite : is-bishop-finite A → is-bishop-finite (Maybe A)
maybe-is-bishop-finite fi = fin₁ do
  aeq ← enumeration₁ fi
  ueq ← enumeration₁ it
  pure $ maybe-as-sum ∙ₑ ⊎-ap ueq aeq ∙ₑ fin-coproduct

instance
  decomp-fin-maybe : goal-decomposition (quote is-bishop-finite) (Maybe A)
  decomp-fin-maybe = decomp (quote maybe-is-bishop-finite) [ `search (quote is-bishop-finite) ]
