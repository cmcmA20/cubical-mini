{-# OPTIONS --safe #-}
module Cubical.Interface.DecEq where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base public

private variable ℓ : Level

record @0 DecEq (A : Type ℓ) : Type ℓ where
  field _≟_ : Discrete A
