{-# OPTIONS --safe #-}
module Foundations.Notation.Commutativity where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Symmetry
open import Foundations.Notation.Transitivity

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
  {ℓx ℓy ℓu ℓv ℓf : Level}
  (X : A → B → 𝒰 ℓx) (Y : B → A → 𝒰 ℓy)
  (U : A → A → 𝒰 ℓu) (V : B → B → 𝒰 ℓv)
  (F : {x : A} {y : B} → V y y → U x x → 𝒰 ℓf) where

  Braidedness
    : (u : Transitivity X Y U) (v : Transitivity Y X V)
    → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓx ⊔ ℓy ⊔ ℓf)
  Braidedness u v = {a : A} {b : B}
                    (p : X a b) (q : Y b a)
                  → F (v q p) (u p q)

  record Braid
    ⦃ t₁ : Trans X Y U ⦄ ⦃ t₂ : Trans Y X V ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓx ⊔ ℓy ⊔ ℓf) where
    no-eta-equality
    field ∙-braid : Braidedness (t₁ ._∙_) (t₂ ._∙_)

open Braid ⦃ ... ⦄ public

-- TODO something funny
-- Braided : (R : A → A → 𝒰 ℓ) ⦃ t : Transitive R ⦄ → Type _
-- Braided R = Braid R R R R {!!}


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where
  Commutativityᵘ : (t : A → A → A) → 𝒰 ℓᵃ
  Commutativityᵘ t = (x y : A) → t y x ＝ t x y

  record Commᵘ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field <>-comm : Commutativityᵘ (t ._<>_)

open Commᵘ ⦃ ... ⦄ public

instance
  Commᵘ→Braid
    : ⦃ _ : Transᵘ A ⦄ ⦃ _ : Commᵘ A ⦄
    → Braid {A = ⊤} {B = ⊤}
        (λ _ _ → A) (λ _ _ → A) (λ _ _ → A) (λ _ _ → A) _＝_
  Commᵘ→Braid .∙-braid = <>-comm
  {-# INCOHERENT Commᵘ→Braid #-}
