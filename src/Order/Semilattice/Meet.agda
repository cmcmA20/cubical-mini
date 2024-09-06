{-# OPTIONS --safe #-}
module Order.Semilattice.Meet where

open import Cat.Prelude

open import Order.Base
open import Order.Diagram.Meet
open import Order.Diagram.Top
import Order.Diagram.Meet.Reasoning as Meets
import Order.Reasoning

record is-meet-semilattice {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  field
    has-top   : Top P
    has-meets : Has-meets P

  open Top has-top public
  open Meets P has-meets public

unquoteDecl H-Level-is-meet-slat =
  declare-record-hlevel 1 H-Level-is-meet-slat (quote is-meet-semilattice)

private variable o ℓ o′ ℓ′ o″ ℓ″ : Level

record
  is-meet-slat-hom
    {P : Poset o ℓ} {Q : Poset o′ ℓ′} (f : P ⇒ Q)
    (P-slat : is-meet-semilattice P)
    (Q-slat : is-meet-semilattice Q) : Type (o ⊔ ℓ′)
  where
  no-eta-equality
  private
    module P = Poset P
    module Pₗ = is-meet-semilattice P-slat
    module Q = Order.Reasoning Q
    module Qₗ = is-meet-semilattice Q-slat

  field
    ⊤-≤ : ⊤ Q.≤ f # ⊤
    ∩-≤ : (x y : P.Ob) → f # x ∩ f # y Q.≤ (f # (x ∩ y))

  pres-⊤ : f # ⊤ ＝ ⊤
  pres-⊤ = Q.≤-antisym Qₗ.! ⊤-≤

  pres-∩ : (x y : P.Ob) → f # (x ∩ y) ＝ (f # x) ∩ (f # y)
  pres-∩ x y = Q.≤-antisym
    (Qₗ.∩-universal _ (f # Pₗ.∩≤l) (f # Pₗ.∩≤r))
    (∩-≤ x y)

  pres-tops
    : ∀ {t}
    → is-top P t
    → is-top Q (f # t)
  pres-tops {t} t-top x =
    x      ~⟨ Qₗ.! ⟩
    ⊤      ~⟨ ⊤-≤ ⟩
    f # ⊤  ~⟨ f # t-top _ ⟩
    f # t  ∎

  pres-meets
    : ∀ {x y m}
    → is-meet P x y m
    → is-meet Q (f # x) (f # y) (f # m)
  pres-meets j .is-meet.meet≤l = f # is-meet.meet≤l j
  pres-meets j .is-meet.meet≤r = f # is-meet.meet≤r j
  pres-meets {x} {y} {m} j .is-meet.greatest ub ub≤fx ub≤fy =
    ub             ~⟨ Qₗ.∩-universal ub ub≤fx ub≤fy ⟩
    f # x ∩ f # y  ~⟨ ∩-≤ x y ⟩
    f # (x ∩ y)    ~⟨ f # j .is-meet.greatest _ Pₗ.∩≤l Pₗ.∩≤r ⟩
    f # m          ∎

unquoteDecl H-Level-is-meet-slat-hom =
  declare-record-hlevel 1 H-Level-is-meet-slat-hom (quote is-meet-slat-hom)

instance
  ⇒-meet-slat : ⇒-notation
    (Σ[ P ꞉ Poset o ℓ ] is-meet-semilattice P) (Σ[ Q ꞉ Poset o′ ℓ′ ] is-meet-semilattice Q) (𝒰 (o ⊔ ℓ ⊔ o′ ⊔ ℓ′))
  ⇒-meet-slat ._⇒_ (P , mp) (Q , mq) = Total-hom Monotone is-meet-slat-hom mp mq

module _ {R : Poset o″ ℓ″} where
  open Order.Reasoning R
  open is-meet-slat-hom

  instance
    Refl-meet-slat-hom : Refl (is-meet-slat-hom {P = R} refl)
    Refl-meet-slat-hom .refl .⊤-≤ = refl
    Refl-meet-slat-hom .refl .∩-≤ _ _ = refl

  module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where instance
    Trans-meet-slat-hom
      : {f : P ⇒ Q} {g : Q ⇒ R}
      → Trans (is-meet-slat-hom f) (is-meet-slat-hom g) (is-meet-slat-hom (f ∙ g))
    Trans-meet-slat-hom {g} ._∙_ α β .⊤-≤ = β .⊤-≤ ∙ g # α .⊤-≤
    Trans-meet-slat-hom {f} {g} ._∙_ α β .∩-≤ x y = β .∩-≤ (f # x) (f # y) ∙ g # α .∩-≤ x y
