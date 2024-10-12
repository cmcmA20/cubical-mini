{-# OPTIONS --safe #-}
module Foundations.Notation.Composition where

open import Foundations.Prim.Type
open import Agda.Builtin.Unit

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _
  {ℓa ℓb ℓc ℓi ℓo ℓ∙ : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb} {C : 𝒰 ℓc}
  (I : A → B → 𝒰 ℓi) (O : B → C → 𝒰 ℓo) (I∙O : A → C → 𝒰 ℓ∙) where

  Composition : {x : A} {y : B} {z : C} (i : I x y) (o : O y z) → 𝒰 ℓ∙
  Composition {x} {y} {z} i o = I∙O x z

  record Comp : 𝒰 (ℓa ⊔ ℓb ⊔ ℓc ⊔ ℓi ⊔ ℓo ⊔ ℓ∙) where
    no-eta-equality
    infixr 30 _∙_
    field _∙_ : {x : A} {y : B} {z : C} (i : I x y) (o : O y z) → Composition i o

    -- FIXME garbage naming
    infixr 9 _∘ˢ_
    _∘ˢ_ : {x : A} {y : B} {z : C} (o : O y z) (i : I x y) → Composition i o
    _∘ˢ_ r l = l ∙ r

open Comp ⦃ ... ⦄ public
{-# DISPLAY Comp._∙_ _ a b = a ∙ b #-}
{-# DISPLAY Comp._∘ˢ_ _ a b = a ∘ˢ b #-}


-- homogeneous composition is transitivity
Trans : (A → A → 𝒰 ℓ) → 𝒰 _
Trans R = Comp R R R


-- unindexed composition is having a chosen binary operation
record Has-binary-op {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  infixr 6 _<>_
  field _<>_ : A → A → A
open Has-binary-op ⦃ ... ⦄ public
{-# DISPLAY Has-binary-op._<>_ _ a b = a <> b #-}


instance
  Has-binary-op→Trans
    : ⦃ Has-binary-op A ⦄
    → Trans {A = ⊤} (λ _ _ → A)
  Has-binary-op→Trans ._∙_ = _<>_
  {-# INCOHERENT Has-binary-op→Trans #-}
