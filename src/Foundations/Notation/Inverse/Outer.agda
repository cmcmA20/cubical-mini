{-# OPTIONS --safe #-}
module Foundations.Notation.Inverse.Outer where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Retract
open import Foundations.Notation.Symmetry
open import Foundations.Notation.Transitivity

private variable
  ℓ : Level
  A : 𝒰 ℓ

-- "left/right inverse" naming is so bad, what's left and right anyway?
-- It depends on composition direction,
-- whereas "inner/outer inverse" are invariant

-- outer
--   v
--   f (g x) ＝ x

-- outer
--   v
--   f ∘ g ＝ id

--   outer
--     v
-- g ∙ f ＝ id

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) (I∙O : A → A → 𝒰 ℓ″) where

  record Inv-o ⦃ r : Refl I∙O ⦄ ⦃ s : Sym O I ⦄ ⦃ t : Trans I O I∙O ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ′ ⊔ ℓ″) where
    no-eta-equality
    field ∙-inv-o : {x : A} {y : B} (p : O y x) → p retract-of sym p

open Inv-o ⦃ ... ⦄ public

Inv-oʰ : (R : A → A → 𝒰 ℓ) ⦃ _ : Refl R ⦄ ⦃ _ : Symʰ R ⦄ ⦃ _ : Transʰ R ⦄ → Type _
Inv-oʰ R = Inv-o R R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where
  Invertibility-lᵘ : (r : A) (s : A → A) (t : A → A → A) → 𝒰 ℓᵃ
  Invertibility-lᵘ r s t = (x : A) → t (s x) x ＝ r

  record Inv-lᵘ ⦃ r : Reflᵘ A ⦄ ⦃ s : Symᵘ A ⦄ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field <>-inv-l : Invertibility-lᵘ (r .mempty) (s .minv) (t ._<>_)

open Inv-lᵘ ⦃ ... ⦄ public

instance
  Inv-lᵘ→Inv-o
    : ⦃ _ : Reflᵘ A ⦄ ⦃ _ : Symᵘ A ⦄ ⦃ _ : Transᵘ A ⦄ ⦃ _ : Inv-lᵘ A ⦄
    → Inv-o {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A) (λ _ _ → A)
  Inv-lᵘ→Inv-o .∙-inv-o = <>-inv-l
  {-# INCOHERENT Inv-lᵘ→Inv-o #-}
