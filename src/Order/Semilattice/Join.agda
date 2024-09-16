{-# OPTIONS --safe #-}
module Order.Semilattice.Join where

open import Cat.Prelude

open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Join
import Order.Diagram.Join.Reasoning as Joins
import Order.Reasoning

record is-join-semilattice {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  field
    has-bottom : Bottom P
    has-joins  : Has-joins P

  open Bottom has-bottom public
  open Joins P has-joins public

unquoteDecl H-Level-is-join-slat =
  declare-record-hlevel 1 H-Level-is-join-slat (quote is-join-semilattice)

private variable o ℓ o′ ℓ′ o″ ℓ″ : Level

record
  is-join-slat-hom
    {P : Poset o ℓ} {Q : Poset o′ ℓ′} (f : P ⇒ Q)
    (P-slat : is-join-semilattice P)
    (Q-slat : is-join-semilattice Q) : Type (o ⊔ ℓ′)
  where
  no-eta-equality
  private
    module P = Poset P
    module Pₗ = is-join-semilattice P-slat
    module Q = Order.Reasoning Q
    module Qₗ = is-join-semilattice Q-slat

  field
    ⊥-≤ : f # ⊥ Q.≤ ⊥
    ∪-≤ : (x y : P.Ob) → f # (x ∪ y) Q.≤ f # x ∪ f # y

  pres-⊥ : f # ⊥ ＝ ⊥
  pres-⊥ = Q.≤-antisym ⊥-≤ Qₗ.¡

  pres-∪ : (x y : P.Ob) → f # (x ∪ y) ＝ (f # x) ∪ (f # y)
  pres-∪ x y = Q.≤-antisym (∪-≤ x y) $ Qₗ.∪-universal _
    (f # Pₗ.l≤∪)
    (f # Pₗ.r≤∪)

  pres-bottoms
    : ∀ {b}
    → is-bottom P b
    → is-bottom Q (f # b)
  pres-bottoms {b} b-bot x =
    f # b  ~⟨ f # b-bot _ ⟩
    f # ⊥  ~⟨ ⊥-≤ ⟩
    ⊥      ~⟨ Qₗ.¡ ⟩
    x      ∎

  pres-joins
    : ∀ {x y m}
    → is-join P x y m
    → is-join Q (f # x) (f # y) (f # m)
  pres-joins j .is-join.l≤join = f # is-join.l≤join j
  pres-joins j .is-join.r≤join = f # is-join.r≤join j
  pres-joins {x} {y} {m} j .is-join.least lb fx≤lb fy≤lb =
    f # m          ~⟨ f # j .is-join.least _ Pₗ.l≤∪  Pₗ.r≤∪ ⟩
    f # (x ∪ y)    ~⟨ ∪-≤ x y ⟩
    f # x ∪ f # y  ~⟨ Qₗ.∪-universal lb fx≤lb fy≤lb ⟩
    lb             ∎

unquoteDecl H-Level-is-join-slat-hom =
  declare-record-hlevel 1 H-Level-is-join-slat-hom (quote is-join-slat-hom)

instance
  ⇒-join-slat : ⇒-notation
    (Σ[ P ꞉ Poset o ℓ ] is-join-semilattice P) (Σ[ Q ꞉ Poset o′ ℓ′ ] is-join-semilattice Q) (𝒰 (o ⊔ ℓ ⊔ o′ ⊔ ℓ′))
  ⇒-join-slat ._⇒_ (P , jp) (Q , jq) = Total-hom Monotone is-join-slat-hom jp jq

module _ {R : Poset o″ ℓ″} where
  open Order.Reasoning R
  open is-join-slat-hom

  instance
    Refl-join-slat-hom : Refl (is-join-slat-hom {P = R} refl)
    Refl-join-slat-hom .refl .⊥-≤ = refl
    Refl-join-slat-hom .refl .∪-≤ _ _ = refl

  module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where instance
    Comp-join-slat-hom
      : {f : P ⇒ Q} {g : Q ⇒ R}
      → Comp (is-join-slat-hom f) (is-join-slat-hom g) (is-join-slat-hom (f ∙ g))
    Comp-join-slat-hom {g} ._∙_ α β .⊥-≤ = g # α .⊥-≤ ∙ β .⊥-≤
    Comp-join-slat-hom {f} {g} ._∙_ α β .∪-≤ x y = g # α .∪-≤ x y ∙ β .∪-≤ (f # x) (f # y)
