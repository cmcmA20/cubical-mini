{-# OPTIONS --safe #-}
module Meta.Effect.Base where

open import Foundations.Base

record Effect : Typeω where
  constructor eff
  field
    {adj} : Level → Level
    ₀     : ∀ {ℓ} → Type ℓ → Type (adj ℓ)
