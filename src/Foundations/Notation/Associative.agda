{-# OPTIONS --safe #-}
module Foundations.Notation.Associative where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Transitive

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ

module _
  {ℓᵃ ℓᵇ ℓᶜ ℓᵈ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ} {D : 𝒰 ℓᵈ}
  {ℓx ℓy ℓz ℓu ℓv ℓw : Level}
  (X : A → B → 𝒰 ℓx) (Y : B → C → 𝒰 ℓy) (Z : C → D → 𝒰 ℓz)
  (U : A → C → 𝒰 ℓu) (V : B → D → 𝒰 ℓv) (W : A → D → 𝒰 ℓw) where

  Associativity
    : (tu : Transitivity X Y U) (tv : Transitivity Y Z V)
      (tw₁ : Transitivity X V W) (tw₂ : Transitivity U Z W)
    → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓᵈ ⊔ ℓx ⊔ ℓy ⊔ ℓz ⊔ ℓw)
  Associativity tu tv tw₁ tw₂ = {a : A} {b : B} {c : C} {d : D}
                                (p : X a b) (q : Y b c) (r : Z c d)
                              → tw₁ p (tv q r) ＝ tw₂ (tu p q) r

  record Assoc
    ⦃ tu  : Trans X Y U ⦄ ⦃ tv  : Trans Y Z V ⦄
    ⦃ tw₁ : Trans X V W ⦄ ⦃ tw₂ : Trans U Z W ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓᵈ ⊔ ℓx ⊔ ℓy ⊔ ℓz ⊔ ℓw) where
    field ∙-assoc : Associativity (tu ._∙_) (tv ._∙_) (tw₁ ._∙_) (tw₂ ._∙_)

open Assoc ⦃ ... ⦄ public

Associative : (R : A → A → 𝒰 ℓ) ⦃ t : Transitive R ⦄ → Type _
Associative R = Assoc R R R R R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where

  Associativityᵘ : (t : A → A → A) → 𝒰 ℓᵃ
  Associativityᵘ t = (x y z : A) → t x (t y z) ＝ t (t x y) z

  record Assocᵘ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    field <>-assoc : Associativityᵘ (t ._<>_)

open Assocᵘ ⦃ ... ⦄ public

instance
  Assocᵘ→Assoc
    : ⦃ _ : Transᵘ A ⦄ ⦃ _ : Assocᵘ A ⦄
    → Assoc {A = ⊤} {B = ⊤} {C = ⊤} {D = ⊤}
        (λ _ _ → A) (λ _ _ → A) (λ _ _ → A)
        (λ _ _ → A) (λ _ _ → A) (λ _ _ → A)
  Assocᵘ→Assoc .∙-assoc = <>-assoc
  {-# INCOHERENT Assocᵘ→Assoc #-}
