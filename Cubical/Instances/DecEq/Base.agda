{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Decidable public

record DecEq {ℓ} (A : Type ℓ) : Type ℓ where
  field _≟_ : Discrete A
open DecEq ⦃ ... ⦄ public
