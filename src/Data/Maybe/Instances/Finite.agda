{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Bind

open import Correspondences.Nullary.Finite.Bishop

open import Data.Maybe.Path
open import Data.Fin.Closure
open import Data.Sum.Properties
open import Data.Unit.Instances.Finite

open import Truncation.Propositional

instance
  maybe-is-fin-set : {ℓ : Level} {A : Type ℓ} → ⦃ is-fin-set A ⦄ → is-fin-set (Maybe A)
  maybe-is-fin-set {A} = fin do
    aeq ← enumeration it
    ueq ← enumeration it
    pure $ maybe-as-sum ∙ₑ ⊎-ap ueq aeq ∙ₑ fin-coproduct
