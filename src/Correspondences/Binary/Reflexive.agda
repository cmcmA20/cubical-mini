{-# OPTIONS --safe #-}
module Correspondences.Binary.Reflexive where

open import Foundations.Prelude
  renaming (refl to reflₚ)

open import Correspondences.Base

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ

-- level-polymorphic, for automation
record Refl {ℓᵃ} {A : 𝒰 ℓᵃ} {ℓ : Level}
  (_~_ : Corr² (A , A) ℓ) : 𝒰 (ℓᵃ ⊔ ℓ) where
  no-eta-equality
  field refl : ∀ {x} → x ~ x

open Refl ⦃ ... ⦄ public

-- homogeneous
Reflexive : Corr² (A , A) ℓ → 𝒰 _
Reflexive = Refl

instance
  Refl-Path : Refl (Path A)
  Refl-Path .refl = reflₚ

  Refl-Fun : Refl (Fun {ℓ})
  Refl-Fun .refl = id

  Refl-≃ : Refl (_≃_ {ℓ})
  Refl-≃ .refl = idₑ

  Refl-≃ᴱ : Refl (_≃ᴱ_ {ℓ})
  Refl-≃ᴱ .refl = ≃→≃ᴱ idₑ

  Refl-Iso : Refl (Iso {ℓ})
  Refl-Iso .refl = idᵢ

-- "untyped" raw reflexivity is just being pointed
record Reflᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field mempty : A

open Reflᵘ ⦃ ... ⦄ public

instance
  Reflᵘ→Refl : ⦃ Reflᵘ A ⦄ → Refl {A = ⊤} λ _ _ → A
  Reflᵘ→Refl .refl = mempty
  {-# INCOHERENT Reflᵘ→Refl #-}
