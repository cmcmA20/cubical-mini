{-# OPTIONS --safe #-}
module Foundations.Size.Base where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties

private variable ℓ ℓ′ ℓ″ ℓ‴ ℓᵃ : Level

-- Resizing of a type

is-of-size : (ℓ′ : Level) → 𝒰 ℓ → 𝒰 (ℓ ⊔ ℓsuc ℓ′)
is-of-size ℓ′ X = Σ[ Y ꞉ 𝒰 ℓ′ ] (Y ≃ X)

is-locally-of-size : (ℓ′ : Level) → 𝒰 ℓ → 𝒰 (ℓ ⊔ ℓsuc ℓ′)
is-locally-of-size ℓ′ X = (x y : X) → is-of-size ℓ′ (x ＝ y)

resizing-cond : {X : 𝒰 ℓ} (s : is-of-size ℓ′ X) → ⌞ s ⌟ ≃ X
resizing-cond {X} = snd

-- TODO move out or rewrite?
-- @0 is-of-size-is-prop : {ℓ′ : Level} {X : 𝒰 ℓ} → is-prop (is-of-size ℓ′ X)
-- is-of-size-is-prop {ℓ} {ℓ′} {X} =
--   ≃→is-of-hlevel 1
--     (Σ-ap-snd λ Y → whisker-bothₑ (lift≃id ⁻¹) (lift≃id ⁻¹) ∙ (=→≃ , univalence) ⁻¹)
--     (lift-is-embedding {ℓ = ℓ′} {ℓ′ = ℓ} (Lift ℓ′ X))


-- Automation

record Size ℓ′ (T : Type ℓ) : Type (ℓ ⊔ ℓsuc ℓ′) where
  no-eta-equality
  constructor size-instance
  field has-of-size : is-of-size ℓ′ T
{-# INLINE size-instance #-}

open Size

size
  : {A : Type ℓᵃ}
  → (ℓ : Level) ⦃ s : Size ℓ A ⦄ → is-of-size ℓ A
size ℓ ⦃ s ⦄ = s .has-of-size

instance
  Size-default : {A : Type ℓ} → Size ℓ A
  Size-default {A} .has-of-size = A , refl
  {-# OVERLAPPABLE Size-default #-}

  Size-big : {A : Type ℓ} → Size (ℓ ⊔ ℓ′) A
  Size-big {ℓ′} {A} .has-of-size = Lift ℓ′ A , lift≃id
  {-# INCOHERENT Size-big #-} -- TODO configure overlaps
