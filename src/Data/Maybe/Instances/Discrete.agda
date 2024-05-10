{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Discrete where

open import Foundations.Base

open import Logic.Discreteness

open import Data.Dec.Base as Dec
open import Data.Maybe.Base
open import Data.Maybe.Path

private variable
  ℓ : Level
  A : Type ℓ

instance
  maybe-is-discrete : ⦃ di : is-discrete A ⦄ → is-discrete (Maybe A)
  maybe-is-discrete {x = nothing} {(nothing)} = yes refl
  maybe-is-discrete {x = nothing} {just _ }   = no nothing≠just
  maybe-is-discrete {x = just _ } {(nothing)} = no $ nothing≠just ∘ sym
  maybe-is-discrete {x = just x } {just y }   = Dec.dmap (ap just) (_∘ just-inj) (x ≟ y)
  {-# OVERLAPPING maybe-is-discrete #-}
