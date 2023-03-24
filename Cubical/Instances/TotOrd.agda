{-# OPTIONS --safe #-}
module Cubical.Instances.TotOrd where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Toset

record TotOrd {ℓ} {ℓ′} (A : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where
  field totOrd : TosetStr ℓ′ A
