{-# OPTIONS --safe #-}
module Correspondences.Binary.Transitive where

open import Foundations.Prelude
  renaming (_∙_ to _∙ₚ_ ; _∘ˢ_ to _∘ₜˢ_)

open import Correspondences.Base

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

-- level-polymorphic, for automation
record Trans {ℓᵃ ℓᵇ ℓᶜ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ} {ℓl ℓr ℓo : Level}
  (L : A → B → 𝒰 ℓl) (R : B → C → 𝒰 ℓr) (O : A → C → 𝒰 ℓo) : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓl ⊔ ℓr ⊔ ℓo) where
  no-eta-equality
  infixr 30 _∙_
  field _∙_ : {x : A} {y : B} {z : C} → L x y → R y z → O x z

  infixr 9 _∘ˢ_
  _∘ˢ_ : {x : A} {y : B} {z : C} → R y z → L x y → O x z
  _∘ˢ_ = flip _∙_

open Trans ⦃ ... ⦄ public

-- homogeneous
Transitive : Corr² (A , A) ℓ → 𝒰 _
Transitive R = Trans R R R

instance
  Trans-Path : Transitive (Path A)
  Trans-Path ._∙_ = _∙ₚ_

  Trans-Fun : Trans (Fun {ℓᵃ} {ℓᵇ}) (Fun {ℓᵇ = ℓᶜ}) Fun
  Trans-Fun ._∙_ f g = g ∘ₜˢ f

  Trans-≃ : Trans (_≃_ {ℓᵃ} {ℓᵇ}) (_≃_ {ℓ' = ℓᶜ}) _≃_
  Trans-≃ ._∙_  = _∙ₑ_

  Trans-≃ᴱ : Trans (_≃ᴱ_ {ℓᵃ} {ℓᵇ}) (_≃ᴱ_ {ℓ′ = ℓᶜ}) _≃ᴱ_
  Trans-≃ᴱ ._∙_  = _∙ᴱₑ_

  Trans-Iso : Trans (Iso {ℓᵃ} {ℓᵇ}) (Iso {ℓ′ = ℓᶜ}) Iso
  Trans-Iso ._∙_  = _∙ᵢ_

-- "untyped" raw transitivity is just having a binary operation
record Transᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  infixr 6 _<>_
  field _<>_ : A → A → A

open Transᵘ ⦃ ... ⦄ public

instance
  Transᵘ→Trans
    : ⦃ Transᵘ A ⦄
    → Trans {A = ⊤} {B = ⊤} {C = ⊤} (λ _ _ → A) (λ _ _ → A) (λ _ _ → A)
  Transᵘ→Trans ._∙_ = _<>_
  {-# INCOHERENT Transᵘ→Trans #-}
