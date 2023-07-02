{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind

open import Meta.Search.Finite.Bishop

open import Data.List.Base
open import Data.Maybe.Path
open import Data.Fin.Closure
open import Data.Sum.Properties
open import Data.Unit.Instances.Finite

open import Truncation.Propositional

private variable
  ℓ : Level
  A : Type ℓ

maybe-is-fin-set : is-fin-set A → is-fin-set (Maybe A)
maybe-is-fin-set fi = fin do
  aeq ← enumeration fi
  ueq ← enumeration it
  pure $ maybe-as-sum ∙ₑ ⊎-ap ueq aeq ∙ₑ fin-coproduct

instance
  decomp-fin-maybe : goal-decomposition (quote is-fin-set-at-hlevel) (Maybe A)
  decomp-fin-maybe = decomp (quote maybe-is-fin-set) (`search (quote is-fin-set-at-hlevel) ∷ [])
