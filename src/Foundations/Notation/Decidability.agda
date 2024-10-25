{-# OPTIONS --safe #-}
module Foundations.Notation.Decidability where

open import Foundations.Prim.Type

record Decidability {ℓ}
  (A : 𝒰 ℓ) : 𝒰ω where
  field
    ℓ-decidability : Level
    Decidable      : A → Type ℓ-decidability
open Decidability ⦃ ... ⦄ public
{-# DISPLAY Decidability.Decidable _ a = Decidable a #-}

record Reflectance {ℓa ℓb}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) : 𝒰ω where
  field
    ℓ-reflectance : Level
    Reflects      : A → B → Type ℓ-reflectance
open Reflectance ⦃ ... ⦄ public
{-# DISPLAY Reflectance.Reflects _ a = Reflects a #-}
