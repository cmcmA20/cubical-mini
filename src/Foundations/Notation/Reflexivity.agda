{-# OPTIONS --safe #-}
module Foundations.Notation.Reflexivity where

open import Foundations.Prim.Type

open import Agda.Builtin.Unit

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _ {ℓa ℓ} {A : 𝒰 ℓa} (_~_ : A → A → 𝒰 ℓ) where
  Reflexivity : 𝒰 (ℓa ⊔ ℓ)
  Reflexivity = ∀ {x} → x ~ x

  record Refl : 𝒰 (ℓa ⊔ ℓ) where
    no-eta-equality
    field refl : Reflexivity

open Refl ⦃ ... ⦄ public
{-# DISPLAY Refl.refl _ = refl #-}


-- unindexed reflexivity is being pointed
record Pointed {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  field mempty : A

open Pointed ⦃ ... ⦄ public
{-# DISPLAY Pointed.mempty _ = mempty #-}

instance
  Pointed→Refl : ⦃ Pointed A ⦄ → Refl {A = ⊤} λ _ _ → A
  Pointed→Refl .refl = mempty
  {-# INCOHERENT Pointed→Refl #-}
