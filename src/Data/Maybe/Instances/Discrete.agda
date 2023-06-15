{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Discrete where

open import Foundations.Base

open import Meta.Decision

import Data.Dec.Base as Dec
open Dec

open import Data.Maybe.Path

-- TODO check if generated one is performant enough
instance
  Discrete-Maybe : {ℓ : Level} {A : Type ℓ} → ⦃ Discrete A ⦄ → Discrete (Maybe A)
  Discrete-Maybe .Decision.has-decidable (just x) (just y) =
    Dec.map (ap just) (λ ¬p p → ¬p (just-inj p)) (x ≟ y)
  Discrete-Maybe .Decision.has-decidable (just x) nothing  = no λ p → nothing≠just (sym p)
  Discrete-Maybe .Decision.has-decidable nothing  (just y) = no nothing≠just
  Discrete-Maybe .Decision.has-decidable nothing  nothing  = yes refl
