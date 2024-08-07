{-# OPTIONS --safe #-}
module Order.Semilattice.Join where

open import Categories.Prelude

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
    (f .pres-≤ Pₗ.l≤∪)
    (f .pres-≤ Pₗ.r≤∪)

  pres-bottoms
    : ∀ {b}
    → is-bottom P b
    → is-bottom Q (f # b)
  pres-bottoms {b} b-bot x =
    f # b  ~⟨ f .pres-≤ (b-bot _) ⟩
    f # ⊥  ~⟨ ⊥-≤ ⟩
    ⊥      ~⟨ Qₗ.¡ ⟩
    x      ∎

  pres-joins
    : ∀ {x y m}
    → is-join P x y m
    → is-join Q (f # x) (f # y) (f # m)
  pres-joins j .is-join.l≤join = f .pres-≤ (is-join.l≤join j)
  pres-joins j .is-join.r≤join = f .pres-≤ (is-join.r≤join j)
  pres-joins {x} {y} {m} j .is-join.least lb fx≤lb fy≤lb =
    f # m          ~⟨ f .pres-≤ (j .is-join.least _ Pₗ.l≤∪  Pₗ.r≤∪) ⟩
    f # (x ∪ y)    ~⟨ ∪-≤ x y ⟩
    f # x ∪ f # y  ~⟨ Qₗ.∪-universal lb fx≤lb fy≤lb ⟩
    lb             ∎

unquoteDecl H-Level-is-join-slat-hom = declare-record-hlevel 1 H-Level-is-join-slat-hom (quote is-join-slat-hom)

open is-join-slat-hom

module _ {R : Poset o ℓ} where
  open Order.Reasoning R

  instance
    Refl-join-slat-hom : Refl (is-join-slat-hom {P = R} refl)
    Refl-join-slat-hom .refl .⊥-≤ = refl
    Refl-join-slat-hom .refl .∪-≤ _ _ = refl

  module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where
    Trans-join-slat-hom
      : {f : P ⇒ Q} {g : Q ⇒ R}
      → Trans (is-join-slat-hom f) (is-join-slat-hom g) (is-join-slat-hom (f ∙ g))
    Trans-join-slat-hom {g} ._∙_ α β .⊥-≤ = g .pres-≤ (α .⊥-≤) ∙ β .⊥-≤
    Trans-join-slat-hom {f} {g} ._∙_ α β .∪-≤ x y = g .pres-≤ (α .∪-≤ x y) ∙ β .∪-≤ (f # x) (f # y)

-- TODO
-- Join-slats-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
-- Join-slats-subcat o ℓ .Subcat.is-ob       = is-join-semilattice
-- Join-slats-subcat o ℓ .Subcat.is-hom      = is-join-slat-hom
-- Join-slats-subcat o ℓ .Subcat.is-hom-prop _ _ _ = hlevel 1
-- Join-slats-subcat o ℓ .Subcat.is-hom-id   = id-join-slat-hom
-- Join-slats-subcat o ℓ .Subcat.is-hom-∘    = ∘-join-slat-hom

-- Join-slats : ∀ o ℓ → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
-- Join-slats o ℓ = Subcategory (Join-slats-subcat o ℓ)

-- module Join-slats {o} {ℓ} = Cat.Reasoning (Join-slats o ℓ)

-- Join-slats→Posets : ∀ {o ℓ} → Functor (Join-slats o ℓ) (Posets o ℓ)
-- Join-slats→Posets = Forget-subcat

-- Join-slats↪Sets : ∀ {o ℓ} → Functor (Join-slats o ℓ) (Sets o)
-- Join-slats↪Sets = Posets↪Sets F∘ Join-slats→Posets

-- Join-semilattice : ∀ o ℓ → Type _
-- Join-semilattice o ℓ = Join-slats.Ob {o} {ℓ}
