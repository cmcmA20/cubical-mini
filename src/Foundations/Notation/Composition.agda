{-# OPTIONS --safe #-}
module Foundations.Notation.Composition where

open import Foundations.Prim.Type
open import Agda.Builtin.Unit

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

module _
  {ℓᵃ ℓᵇ ℓᶜ ℓi ℓo ℓ∙ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
  (I : A → B → 𝒰 ℓi) (O : B → C → 𝒰 ℓo) (I∙O : A → C → 𝒰 ℓ∙) where

  Composition : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓi ⊔ ℓo ⊔ ℓ∙)
  Composition = {x : A} {y : B} {z : C} → I x y → O y z → I∙O x z

  record Comp : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓi ⊔ ℓo ⊔ ℓ∙) where
    no-eta-equality
    infixr 30 _∙_
    field _∙_ : Composition

    -- FIXME garbage naming
    infixr 9 _∘ˢ_
    _∘ˢ_ : {x : A} {y : B} {z : C} → O y z → I x y → I∙O x z
    _∘ˢ_ r l = l ∙ r

open Comp ⦃ ... ⦄ public


-- homogeneous composition is transitivity
Trans : (A → A → 𝒰 ℓ) → 𝒰 _
Trans R = Comp R R R


-- unindexed composition is having a chosen binary operation
record Has-binary-op {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  infixr 6 _<>_
  field _<>_ : A → A → A
open Has-binary-op ⦃ ... ⦄ public


instance
  Has-binary-op→Trans
    : ⦃ Has-binary-op A ⦄
    → Trans {A = ⊤} (λ _ _ → A)
  Has-binary-op→Trans ._∙_ = _<>_
  {-# INCOHERENT Has-binary-op→Trans #-}
