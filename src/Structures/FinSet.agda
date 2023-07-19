{-# OPTIONS --safe #-}
module Structures.FinSet where

open import Foundations.Base

open import Meta.Underlying public

open import Correspondences.Finite.Bishop

private variable
  ℓ : Level
  A : Type ℓ

record FinSet (ℓ : Level) : Type (ℓsuc ℓ) where
  constructor fin-set
  field
    carrier : Type ℓ
    carrier-is-fin-set : is-fin-set carrier

open FinSet

instance
  Underlying-FinSet : Underlying (FinSet ℓ)
  Underlying-FinSet {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-FinSet .⌞_⌟ = carrier
