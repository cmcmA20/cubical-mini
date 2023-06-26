{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Discrete where

open import Foundations.Base

open import Correspondences.Nullary.Decidable

import Data.Dec.Base as Dec
open Dec

open import Data.Maybe.Path

-- TODO check if generated one is performant enough
instance
  maybe-is-discrete : {ℓ : Level} {A : Type ℓ} → ⦃ is-discrete A ⦄ → is-discrete (Maybe A)
  maybe-is-discrete = is-discrete-η go where
    go : _
    go (just x) (just y) =
      Dec.map (ap just) (λ ¬p p → ¬p (just-inj p)) (x ≟ y)
    go (just x) nothing  = no λ p → nothing≠just (sym p)
    go nothing  (just y) = no nothing≠just
    go nothing  nothing  = yes refl
