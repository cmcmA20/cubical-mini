{-# OPTIONS --safe #-}
module Foundations.Notation.Transitivity where

open import Foundations.Prim.Type
open import Agda.Builtin.Unit

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

module _
  {ℓᵃ ℓᵇ ℓᶜ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ} {ℓi ℓo ℓ∙ : Level}
  (I : A → B → 𝒰 ℓi) (O : B → C → 𝒰 ℓo) (I∙O : A → C → 𝒰 ℓ∙) where

  Transitivity : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓi ⊔ ℓo ⊔ ℓ∙)
  Transitivity = {x : A} {y : B} {z : C} → I x y → O y z → I∙O x z

  record Trans : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓi ⊔ ℓo ⊔ ℓ∙) where
    no-eta-equality
    infixr 30 _∙_
    field _∙_ : Transitivity

    -- FIXME garbage naming
    infixr 9 _∘ˢ_
    _∘ˢ_ : {x : A} {y : B} {z : C} → O y z → I x y → I∙O x z
    _∘ˢ_ r l = l ∙ r

open Trans ⦃ ... ⦄ public

Transʰ : (A → A → 𝒰 ℓ) → 𝒰 _
Transʰ R = Trans R R R


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

  Trans-⊤ : {D : A → B → 𝒰 ℓ} {E : B → C → 𝒰 ℓ′} → Trans {C = C} D E (λ _ _ → ⊤)
  Trans-⊤ ._∙_ _ _ = tt
  {-# INCOHERENT Trans-⊤ #-}
