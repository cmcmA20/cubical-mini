{-# OPTIONS --safe #-}
module Foundations.Notation.Decidability where

open import Foundations.Prim.Type

record Decidability {ℓᵃ}
  (A : 𝒰 ℓᵃ) : 𝒰ω where
  field
    ℓ-decidability : Level
    Decidable      : A → Type ℓ-decidability
open Decidability ⦃ ... ⦄ public
{-# DISPLAY Decidability.Decidable _ a = Decidable a #-}

record Reflectance {ℓᵃ ℓᵇ}
  (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) : 𝒰ω where
  field
    ℓ-reflectance : Level
    Reflects      : A → B → Type ℓ-reflectance
open Reflectance ⦃ ... ⦄ public
{-# DISPLAY Reflectance.Reflects _ a = Reflects a #-}

private variable ℓ ℓ′ ℓ″ : Level

instance
  Decidability-Variadic
    : {A : Type ℓ} {X : Type ℓ′}
      ⦃ de : Decidability A ⦄
    → Decidability (X → A)
  Decidability-Variadic {ℓ′} {X} ⦃ de ⦄ .ℓ-decidability =
    ℓ′ ⊔ de .Decidability.ℓ-decidability
  Decidability-Variadic {X} ⦃ de ⦄ .Decidable f =
    {x : X} → de .Decidable (f x)
  {-# OVERLAPS Decidability-Variadic #-}

  Reflectance-Variadic
    : {A : Type ℓ} {B : Type ℓ′} {X : Type ℓ″}
      ⦃ re : Reflectance A B ⦄
    → Reflectance (X → A) (X → B)
  Reflectance-Variadic {ℓ″} ⦃ re ⦄ .ℓ-reflectance =
    ℓ″ ⊔ re .Reflectance.ℓ-reflectance
  Reflectance-Variadic {X} ⦃ re ⦄ .Reflects f b =
    (x : X) → re .Reflects (f x) (b x)
  {-# OVERLAPS Reflectance-Variadic #-}
