{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

import Data.Dec.Base as Dec
open Dec
open import Data.List.Base
open import Data.Maybe.Path

private variable
  ℓ : Level
  A : Type ℓ

opaque
  unfolding is-decidable-at-hlevel
  -- TODO wtf is this, check if it's useful
  maybe-decision : Decision A → Decision (Maybe A)
  maybe-decision = Dec.rec (yes ∘ just) λ _ → yes nothing

  maybe-is-discrete : is-discrete A → is-discrete (Maybe A)
  maybe-is-discrete _ nothing nothing  = yes refl
  maybe-is-discrete _ nothing (just _) = no nothing≠just
  maybe-is-discrete _ (just _) nothing = no $ nothing≠just ∘ sym
  maybe-is-discrete di (just x) (just y) =
    Dec.map (ap just) (_∘ just-inj) (di x y)

instance
  decomp-dec₀-maybe : goal-decomposition (quote is-decidable-at-hlevel) (Maybe A)
  decomp-dec₀-maybe = decomp (quote maybe-decision) (`search (quote is-decidable-at-hlevel) ∷ [])

  decomp-dec₁-maybe : goal-decomposition (quote is-decidable-at-hlevel) (Maybe A)
  decomp-dec₁-maybe = decomp (quote maybe-is-discrete) (`search (quote is-decidable-at-hlevel) ∷ [])
