{-# OPTIONS --safe #-}
module Foundations.Notation.Associativity where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Composition

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ

module _
  {ℓᵃ ℓᵇ ℓᶜ ℓᵈ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ} {D : 𝒰 ℓᵈ}
  {ℓx ℓy ℓz ℓu ℓv ℓw : Level}
  (X : A → B → 𝒰 ℓx) (Y : B → C → 𝒰 ℓy) (Z : C → D → 𝒰 ℓz)
  (U : A → C → 𝒰 ℓu) (V : B → D → 𝒰 ℓv) (W : A → D → 𝒰 ℓw) where

  GAssociativity
    : (tu : Composition X Y U) (tv : Composition Y Z V)
      (tw₁ : Composition X V W) (tw₂ : Composition U Z W)
    → {a : A} {b : B} {c : C} {d : D}
    → (p : X a b) (q : Y b c) (r : Z c d)
    → 𝒰 ℓw
  GAssociativity tu tv tw₁ tw₂ p q r = tw₁ p (tv q r) ＝ tw₂ (tu p q) r

  record GAssoc
    ⦃ tu  : Comp X Y U ⦄ ⦃ tv  : Comp Y Z V ⦄
    ⦃ tw₁ : Comp X V W ⦄ ⦃ tw₂ : Comp U Z W ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓᵈ ⊔ ℓx ⊔ ℓy ⊔ ℓz ⊔ ℓw) where
    no-eta-equality
    field ∙-assoc : ∀{a b c d} (p : X a b) (q : Y b c) (r : Z c d)
                  → GAssociativity (tu ._∙_) (tv ._∙_) (tw₁ ._∙_) (tw₂ ._∙_) p q r

open GAssoc ⦃ ... ⦄ public


-- associativity of homogeneous correspondence
HAssoc : (R : A → A → 𝒰 ℓ) ⦃ t : Trans R ⦄ → Type _
HAssoc R = GAssoc R R R R R R


-- associativity of binary operator
module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where

  Associativity : (t : A → A → A) (x y z : A) → 𝒰 ℓᵃ
  Associativity t x y z = t x (t y z) ＝ t (t x y) z

  record Assoc ⦃ t : Has-binary-op A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field <>-assoc : ∀ x y z → Associativity (t ._<>_) x y z

open Assoc ⦃ ... ⦄ public

instance
  Assoc→HAssoc
    : ⦃ _ : Has-binary-op A ⦄ ⦃ _ : Assoc A ⦄
    → HAssoc {A = ⊤} (λ _ _ → A)
  Assoc→HAssoc .∙-assoc = <>-assoc
  {-# INCOHERENT Assoc→HAssoc #-}
