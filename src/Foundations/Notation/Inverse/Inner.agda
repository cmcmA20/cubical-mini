{-# OPTIONS --safe #-}
module Foundations.Notation.Inverse.Inner where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Section
open import Foundations.Notation.Symmetry
open import Foundations.Notation.Transitivity

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

-- "left/right inverse" naming is so bad, what's left and right anyway?
-- It depends on composition direction,
-- whereas "inner/outer inverse" are invariant

--  inner
--    v
-- f (g x) ＝ x

--   inner
--     v
-- f ∘ g ＝ id

-- inner
--   v
--   g ∙ f ＝ id

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) (I∙O : A → A → 𝒰 ℓ″) where

  record Inv-i ⦃ r : Refl I∙O ⦄ ⦃ s : Sym I O ⦄ ⦃ t : Trans I O I∙O ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ″) where
    no-eta-equality
    field ∙-inv-i : {x : A} {y : B} (p : I x y) → p section-of sym p

open Inv-i ⦃ ... ⦄ public

Inv-iʰ : (R : A → A → 𝒰 ℓ) ⦃ _ : Refl R ⦄ ⦃ _ : Symʰ R ⦄ ⦃ _ : Transʰ R ⦄ → Type _
Inv-iʰ R = Inv-i R R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where
  Invertibility-rᵘ : (r : A) (s : A → A) (t : A → A → A) → 𝒰 ℓᵃ
  Invertibility-rᵘ r s t = (x : A) → t x (s x) ＝ r

  record Inv-rᵘ ⦃ r : Reflᵘ A ⦄ ⦃ s : Symᵘ A ⦄ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field <>-inv-r : Invertibility-rᵘ (r .mempty) (s .minv) (t ._<>_)

open Inv-rᵘ ⦃ ... ⦄ public

instance
  Inv-rᵘ→Inv-i
    : ⦃ _ : Reflᵘ A ⦄ ⦃ _ : Symᵘ A ⦄ ⦃ _ : Transᵘ A ⦄ ⦃ _ : Inv-rᵘ A ⦄
    → Inv-i {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A) (λ _ _ → A)
  Inv-rᵘ→Inv-i .∙-inv-i = <>-inv-r
  {-# INCOHERENT Inv-rᵘ→Inv-i #-}
