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
{-# DISPLAY Refl.refl _ = refl #-}


-- unindexed reflexivity is being pointed
record Pointed {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field mempty : A

open Pointed ⦃ ... ⦄ public
{-# DISPLAY Pointed.mempty _ = mempty #-}

instance
  Pointed→Refl : ⦃ Pointed A ⦄ → Refl {A = ⊤} λ _ _ → A
  Pointed→Refl .refl = mempty
  {-# INCOHERENT Pointed→Refl #-}
