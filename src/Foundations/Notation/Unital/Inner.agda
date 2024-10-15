{-# OPTIONS --safe #-}
module Foundations.Notation.Unital.Inner where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition
open import Foundations.Notation.Reflexivity

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _
  {ℓa ℓb ℓb∙ ℓh : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  (L : A → B → 𝒰 ℓh) (R : B → B → 𝒰 ℓb∙) where

  GUnitality-i
    : {x : A} {y : B} (p : L x y)
      (r : Reflexivity R) (t : Composition L R L p r)
    → 𝒰 ℓh
  GUnitality-i p r t = t ＝ p

  record GUnit-i ⦃ r : Refl R ⦄ ⦃ t : Comp L R L ⦄ : 𝒰 (ℓa ⊔ ℓb ⊔ ℓb∙ ⊔ ℓh) where
    no-eta-equality
    field ∙-id-i : ∀{x y} (p : L x y) → GUnitality-i p (r .refl) (t ._∙_ p refl)

open GUnit-i ⦃ ... ⦄ public

-- inner unitality of homogeneous correspondence
HUnit-i : (R : A → A → 𝒰 ℓ) ⦃ r : Refl R ⦄ ⦃ t : Trans R ⦄ → Type _
HUnit-i R = GUnit-i R R


-- right unitality of binary operator
module _ {ℓ} (A : 𝒰 ℓ) where

  Unitality-r : (r : A) (t : A → A → A) (x : A) → 𝒰 ℓ
  Unitality-r r t x = t x r ＝ x

  record Unit-r ⦃ r : Pointed A ⦄ ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓ where
    no-eta-equality
    field <>-id-r : ∀ x → Unitality-r (r .mempty) (t ._<>_) x

open Unit-r ⦃ ... ⦄ public

instance
  Unit-r→HUnit-i
    : ⦃ _ : Pointed A ⦄ ⦃ _ : Has-binary-op A ⦄ ⦃ _ : Unit-r A ⦄
    → HUnit-i {A = ⊤} (λ _ _ → A)
  Unit-r→HUnit-i .∙-id-i = <>-id-r
  {-# INCOHERENT Unit-r→HUnit-i #-}
