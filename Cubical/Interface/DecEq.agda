{-# OPTIONS --safe #-}
module Cubical.Interface.DecEq where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete; Dec; yes; no) public

private variable ℓ : Level

record DecEq (A : Type ℓ) : Type ℓ where
  field _≟_ : Discrete A
