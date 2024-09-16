{-# OPTIONS --safe #-}
module Foundations.Notation.Unital.Inner where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition
open import Foundations.Notation.Reflexivity

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓl ℓr : Level}
  (L : A → B → 𝒰 ℓl) (R : B → B → 𝒰 ℓr) where

  GUnitality-i
    : (r : Reflexivity R) (t : Composition L R L)
    → {x : A} {y : B} (p : L x y)
    → 𝒰 ℓl
  GUnitality-i r t p = t p r ＝ p

  record GUnit-i ⦃ r : Refl R ⦄ ⦃ t : Comp L R L ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓl ⊔ ℓr) where
    no-eta-equality
    field ∙-id-i : ∀{x y} (p : L x y) → GUnitality-i (r .refl) (t ._∙_) p

open GUnit-i ⦃ ... ⦄ public

-- inner unitality of homogeneous correspondence
HUnit-i : (R : A → A → 𝒰 ℓ) ⦃ r : Refl R ⦄ ⦃ t : Trans R ⦄ → Type _
HUnit-i R = GUnit-i R R


-- right unitality of binary operator
module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where

  Unitality-r : (r : A) (t : A → A → A) (x : A) → 𝒰 ℓᵃ
  Unitality-r r t x = t x r ＝ x

  record Unit-r ⦃ r : Pointed A ⦄ ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field <>-id-r : ∀ x → Unitality-r (r .mempty) (t ._<>_) x

open Unit-r ⦃ ... ⦄ public

instance
  Unit-r→HUnit-i
    : ⦃ _ : Pointed A ⦄ ⦃ _ : Has-binary-op A ⦄ ⦃ _ : Unit-r A ⦄
    → HUnit-i {A = ⊤} (λ _ _ → A)
  Unit-r→HUnit-i .∙-id-i = <>-id-r
  {-# INCOHERENT Unit-r→HUnit-i #-}
