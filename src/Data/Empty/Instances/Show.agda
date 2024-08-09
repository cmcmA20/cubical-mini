{-# OPTIONS --safe #-}
module Data.Empty.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Empty.Base

instance
  Show-⊥ : Show ⊥
  Show-⊥ = default-show λ _ → "Guru meditation"

  Show-absurd : ∀{ℓ}{A : Type ℓ} → Show (¬ A)
  Show-absurd = default-show λ _ → "<↯>"
  {-# OVERLAPPING Show-absurd #-}
