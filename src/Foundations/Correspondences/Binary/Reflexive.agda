{-# OPTIONS --safe #-}
module Foundations.Correspondences.Binary.Reflexive where

open import Foundations.Prim.Type

open import Agda.Builtin.Unit

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ

-- level-polymorphic, for automation
record Refl {ℓᵃ} {A : 𝒰 ℓᵃ} {ℓ : Level}
  (_~_ : A → A → 𝒰 ℓ) : 𝒰 (ℓᵃ ⊔ ℓ) where
  no-eta-equality
  field refl : ∀ {x} → x ~ x

open Refl ⦃ ... ⦄ public

-- homogeneous
Reflexive : (A → A → 𝒰 ℓ) → 𝒰 _
Reflexive = Refl


-- "untyped" raw reflexivity is just being pointed
record Reflᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field mempty : A

open Reflᵘ ⦃ ... ⦄ public

instance
  Reflᵘ→Refl : ⦃ Reflᵘ A ⦄ → Refl {A = ⊤} λ _ _ → A
  Reflᵘ→Refl .refl = mempty
  {-# INCOHERENT Reflᵘ→Refl #-}
