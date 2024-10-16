{-# OPTIONS --safe #-}
module Foundations.Notation.Unital.Outer where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition
open import Foundations.Notation.Reflexivity

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _
  {ℓa ℓa∙ ℓb ℓh : Level} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
  (L : A → A → 𝒰 ℓa∙) (R : A → B → 𝒰 ℓh) where

  GUnitality-o
    : {x : A} {y : B} (q : R x y)
      (r : Reflexivity L) (t : Composition L R R r q)
    → 𝒰 ℓh
  GUnitality-o q r t = t ＝ q

  record GUnit-o ⦃ r : Refl L ⦄ ⦃ t : Comp L R R ⦄ : 𝒰 (ℓa ⊔ ℓa∙ ⊔ ℓb ⊔ ℓh) where
    no-eta-equality
    field ∙-id-o : ∀ {x y} (q : R x y) → GUnitality-o q (r .refl) (t ._∙_ refl q)

open GUnit-o ⦃ ... ⦄ public

-- outer unitality of homogeneous correspondence
HUnit-o : (R : A → A → 𝒰 ℓ) ⦃ r : Refl R ⦄ ⦃ t : Trans R ⦄ → Type _
HUnit-o R = GUnit-o R R


-- left unitality of binary operator
module _ {ℓ} (A : 𝒰 ℓ) where

  Unitality-l : (r : A) (t : A → A → A) (x : A) → 𝒰 ℓ
  Unitality-l r t x = t r x ＝ x

  record Unit-l ⦃ r : Pointed A ⦄ ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓ where
    no-eta-equality
    field <>-id-l : ∀ x → Unitality-l (r .mempty) (t ._<>_) x

open Unit-l ⦃ ... ⦄ public

instance
  Unit-l→HUnit-o
    : ⦃ _ : Pointed A ⦄ ⦃ _ : Has-binary-op A ⦄ ⦃ _ : Unit-l A ⦄
    → HUnit-o {A = ⊤} (λ _ _ → A)
  Unit-l→HUnit-o .∙-id-o = <>-id-l
  {-# INCOHERENT Unit-l→HUnit-o #-}
