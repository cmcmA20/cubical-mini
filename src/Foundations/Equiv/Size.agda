{-# OPTIONS --safe #-}
module Foundations.Equiv.Size where

open import Foundations.Base
open import Foundations.HLevel.Base
open import Foundations.HLevel.Closure
open import Foundations.Univalence.Base

open import Foundations.Sigma.Properties
open import Functions.Embedding

open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Equiv.Groupoid

private variable
  ℓ ℓ′ ℓ″ : Level

-- Resizing of a type

has-size : (ℓ′ : Level) → 𝒰 ℓ → 𝒰 (ℓ ⊔ ℓsuc ℓ′)
has-size ℓ′ X = Σ[ Y ꞉ 𝒰 ℓ′ ] (Y ≃ X)

@0 has-size-is-prop : {ℓ′ : Level} {X : 𝒰 ℓ} → is-prop (has-size ℓ′ X)
has-size-is-prop {ℓ} {ℓ′} {X} =
  ≃→is-of-hlevel 1
    (Σ-ap-snd λ Y → whisker-bothₑ (lift≃id ⁻¹) (lift≃id ⁻¹) ∙ (=→≃ , univalence) ⁻¹)
    (lift-is-embedding {ℓ = ℓ′} {ℓ′ = ℓ} (Lift ℓ′ X))

id-size : {X : 𝒰 ℓ} → has-size ℓ X
id-size {X} = X , refl

resized : {X : 𝒰 ℓ} → has-size ℓ′ X → 𝒰 ℓ′
resized {X} = fst

resizing-cond : {X : 𝒰 ℓ} → (s : has-size ℓ′ X) → resized s ≃ X
resizing-cond {X} = snd

resize-up : {X : 𝒰 ℓ} → has-size (ℓ ⊔ ℓ′) X
resize-up {ℓ′} {X} = Lift ℓ′ X , lift≃id
