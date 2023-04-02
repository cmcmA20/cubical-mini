{-# OPTIONS --safe #-}
module Cubical.Instances.TotOrd.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Toset public

record TotOrd {ℓ ℓ′} (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ′)) where
  field tos : TosetStr ℓ′ A
  open TosetStr tos public

open TotOrd ⦃ ... ⦄ using (_≤?_) public

-- TODO: add trichotomous version
