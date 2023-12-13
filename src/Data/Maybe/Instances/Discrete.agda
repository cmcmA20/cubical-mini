{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base as Dec
open import Data.Maybe.Base
open import Data.Maybe.Path

private variable
  ℓ : Level
  A : Type ℓ

maybe-is-discrete : is-discrete A → is-discrete (Maybe A)
maybe-is-discrete di = is-discrete-η λ where
  nothing  nothing → yes refl
  nothing  (just _) → no nothing≠just
  (just _) nothing → no $ nothing≠just ∘ sym
  (just x) (just y) → Dec.dmap (ap just) (_∘ just-inj) (is-discrete-β di x y)

instance
  decomp-dis-maybe : goal-decomposition (quote is-discrete) (Maybe A)
  decomp-dis-maybe = decomp (quote maybe-is-discrete) [ `search (quote is-discrete) ]
