{-# OPTIONS --safe #-}
module Data.Unit.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Dec.Base
open import Data.Unit.Base public

instance
  opaque
    unfolding is-decidable-at-hlevel
    ⊤-decision : Decision ⊤
    ⊤-decision = yes tt

  ⊤-is-discrete : is-discrete ⊤
  ⊤-is-discrete = is-discrete-η λ _ _ → yes refl
