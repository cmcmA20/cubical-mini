{-# OPTIONS --safe #-}
module Foundations.Notation.Reflexivity where

open import Foundations.Prim.Type

open import Agda.Builtin.Unit

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ

module _ {ℓᵃ} {A : 𝒰 ℓᵃ} {ℓ : Level} (_~_ : A → A → 𝒰 ℓ) where
  Reflexivity : 𝒰 (ℓᵃ ⊔ ℓ)
  Reflexivity = ∀ {x} → x ~ x

  record Refl : 𝒰 (ℓᵃ ⊔ ℓ) where
    no-eta-equality
    field refl : Reflexivity

open Refl ⦃ ... ⦄ public


-- "untyped" raw reflexivity is just being pointed
record Reflᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field mempty : A

open Reflᵘ ⦃ ... ⦄ public

instance
  Reflᵘ→Refl : ⦃ Reflᵘ A ⦄ → Refl {A = ⊤} λ _ _ → A
  Reflᵘ→Refl .refl = mempty
  {-# INCOHERENT Reflᵘ→Refl #-}
