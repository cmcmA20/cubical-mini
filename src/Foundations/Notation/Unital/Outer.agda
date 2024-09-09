{-# OPTIONS --safe #-}
module Foundations.Notation.Unital.Outer where

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
  (L : A → A → 𝒰 ℓl) (R : A → B → 𝒰 ℓr) where

  GUnitality-o
    : (r : Reflexivity L) (t : Composition L R R)
      {x : A} {y : B} (q : R x y)
    → 𝒰 ℓr
  GUnitality-o r t q = t r q ＝ q

  record GUnit-o ⦃ r : Refl L ⦄ ⦃ t : Comp L R R ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓl ⊔ ℓr) where
    no-eta-equality
    field ∙-id-o : ∀ {x y} (q : R x y) → GUnitality-o (r .refl) (t ._∙_) q

open GUnit-o ⦃ ... ⦄ public

-- outer unitality of homogeneous correspondence
HUnit-o : (R : A → A → 𝒰 ℓ) ⦃ r : Refl R ⦄ ⦃ t : Trans  R ⦄ → Type _
HUnit-o R = GUnit-o R R


-- left unitality of binary operator
module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where

  Unitality-l : (r : A) (t : A → A → A) (x : A) → 𝒰 ℓᵃ
  Unitality-l r t x = t r x ＝ x

  record Unit-l ⦃ r : Pointed A ⦄ ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field <>-id-l : ∀ x → Unitality-l (r .mempty) (t ._<>_) x

open Unit-l ⦃ ... ⦄ public

instance
  Unit-l→HUnit-o
    : ⦃ _ : Pointed A ⦄ ⦃ _ : Has-binary-op A ⦄ ⦃ _ : Unit-l A ⦄
    → HUnit-o {A = ⊤} (λ _ _ → A)
  Unit-l→HUnit-o .∙-id-o = <>-id-l
  {-# INCOHERENT Unit-l→HUnit-o #-}
