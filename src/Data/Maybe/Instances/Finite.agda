{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Finite where

open import Foundations.Base

open import Meta.Bind
open import Meta.Finite

open import Data.Maybe.Path
open import Data.Fin.Closure
open import Data.Sum.Properties
open import Data.Unit.Instances.Finite

open import Truncation.Propositional

instance
  Finite-Maybe : {ℓ : Level} {A : Type ℓ} → ⦃ Finite A ⦄ → Finite (Maybe A)
  Finite-Maybe {A} = fin do
    aeq ← enumeration {T = A}
    ueq ← enumeration {T = ⊤}
    pure (maybe-as-sum ∙ₑ ⊎-ap ueq aeq ∙ₑ fin-coproduct)
