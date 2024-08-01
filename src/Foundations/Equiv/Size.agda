{-# OPTIONS --safe #-}
module Foundations.Equiv.Size where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties

private variable ℓ ℓ′ ℓ″ ℓ‴ : Level

-- Resizing of a type

is-of-size : (ℓ′ : Level) → 𝒰 ℓ → 𝒰 (ℓ ⊔ ℓsuc ℓ′)
is-of-size ℓ′ X = Σ[ Y ꞉ 𝒰 ℓ′ ] (Y ≃ X)

-- TODO move out or rewrite?
-- @0 is-of-size-is-prop : {ℓ′ : Level} {X : 𝒰 ℓ} → is-prop (is-of-size ℓ′ X)
-- is-of-size-is-prop {ℓ} {ℓ′} {X} =
--   ≃→is-of-hlevel 1
--     (Σ-ap-snd λ Y → whisker-bothₑ (lift≃id ⁻¹) (lift≃id ⁻¹) ∙ (=→≃ , univalence) ⁻¹)
--     (lift-is-embedding {ℓ = ℓ′} {ℓ′ = ℓ} (Lift ℓ′ X))

id-size : {X : 𝒰 ℓ} → is-of-size ℓ X
id-size {X} = X , refl

resizing-cond : {X : 𝒰 ℓ} → (s : is-of-size ℓ′ X) → ⌞ s ⌟ ≃ X
resizing-cond {X} = snd

resize-up : {X : 𝒰 ℓ} → is-of-size (ℓ ⊔ ℓ′) X
resize-up {ℓ′} {X} = Lift ℓ′ X , lift≃id

≃→is-of-size : {X : 𝒰 ℓ} {Y : 𝒰 ℓ′}
             → X ≃ Y
             → is-of-size ℓ″ X → is-of-size ℓ″ Y
≃→is-of-size e (X' , ex) = (X' , ex ∙ e)

is-locally-of-size : (ℓ′ : Level) → 𝒰 ℓ → 𝒰 (ℓ ⊔ ℓsuc ℓ′)
is-locally-of-size ℓ′ X = (x y : X) → is-of-size ℓ′ (x ＝ y)
