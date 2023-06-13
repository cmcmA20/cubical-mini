{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete

import Data.Dec.Base as Dec

open import Data.Maybe.Path

-- TODO check if generated one is performant enough
instance
  Discrete-Maybe : {ℓ : Level} {A : Type ℓ} → ⦃ Discrete A ⦄ → Discrete (Maybe A)
  Discrete-Maybe .Discrete._≟_ (just x) (just y) =
    Dec.map (ap just) (λ ¬p p → ¬p (just-inj p)) (x ≟ y)
  Discrete-Maybe .Discrete._≟_ (just x) nothing  = no λ p → nothing≠just (sym p)
  Discrete-Maybe .Discrete._≟_ nothing  (just y) = no nothing≠just
  Discrete-Maybe .Discrete._≟_ nothing  nothing  = yes refl
