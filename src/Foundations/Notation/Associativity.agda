{-# OPTIONS --safe #-}
module Foundations.Notation.Associativity where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition

private variable
  ℓ : Level
  A : 𝒰 ℓ

module _
  {ℓa ℓb ℓc ℓd ℓx ℓy ℓz ℓu ℓv ℓw : Level}
  {A : 𝒰 ℓa} {B : 𝒰 ℓb} {C : 𝒰 ℓc} {D : 𝒰 ℓd}
  (X : A → B → 𝒰 ℓx) (Y : B → C → 𝒰 ℓy) (Z : C → D → 𝒰 ℓz)
  (U : A → C → 𝒰 ℓu) (V : B → D → 𝒰 ℓv) (W : A → D → 𝒰 ℓw) where

  GAssociativity
    : {a : A} {b : B} {c : C} {d : D}
      (p : X a b) (q : Y b c) (r : Z c d)
      (tu : Composition X Y U p q) (tv : Composition Y Z V q r)
      (tw₁ : Composition X V W p tv) (tw₂ : Composition U Z W tu r)
    → 𝒰 ℓw
  GAssociativity p q r tu tv tw₁ tw₂ = tw₁ ＝ tw₂

  record GAssoc
    ⦃ tu  : Comp X Y U ⦄ ⦃ tv  : Comp Y Z V ⦄
    ⦃ tw₁ : Comp X V W ⦄ ⦃ tw₂ : Comp U Z W ⦄ : 𝒰 (ℓa ⊔ ℓb ⊔ ℓc ⊔ ℓd ⊔ ℓx ⊔ ℓy ⊔ ℓz ⊔ ℓw) where
    no-eta-equality
    field ∙-assoc : ∀{a b c d} (p : X a b) (q : Y b c) (r : Z c d)
                  → GAssociativity p q r (p ∙ q) (q ∙ r) (p ∙ q ∙ r) ((p ∙ q) ∙ r)

open GAssoc ⦃ ... ⦄ public


-- associativity of homogeneous correspondence
HAssoc : (R : A → A → 𝒰 ℓ) ⦃ t : Trans R ⦄ → Type _
HAssoc R = GAssoc R R R R R R


-- associativity of binary operator
module _ {ℓ} (A : 𝒰 ℓ) where

  Associativity : (t : A → A → A) (x y z : A) → 𝒰 ℓ
  Associativity t x y z = t x (t y z) ＝ t (t x y) z

  record Assoc ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓ where
    no-eta-equality
    field <>-assoc : ∀ x y z → Associativity (t ._<>_) x y z

open Assoc ⦃ ... ⦄ public

instance
  Assoc→HAssoc
    : ⦃ _ : Has-binary-op A ⦄ ⦃ _ : Assoc A ⦄
    → HAssoc {A = ⊤} (λ _ _ → A)
  Assoc→HAssoc .∙-assoc = <>-assoc
  {-# INCOHERENT Assoc→HAssoc #-}
