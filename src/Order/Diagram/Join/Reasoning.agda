{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Join
open import Order.Diagram.Top

module Order.Diagram.Join.Reasoning
  {o ℓ} (P : Poset o ℓ) (hj : Has-joins P)
  where

open import Algebra.Semigroup
open import Cat.Prelude

open Poset P
open Join

instance
  Union-Poset : Union Ob Ob Ob
  Union-Poset ._∪_ x y = hj {x} {y} .lub

joins : ∀ x y → Join P x y
joins x y .lub      = x ∪ y
joins x y .has-join = hj .has-join

module joins {x} {y} = Join (joins x y)
open joins renaming
  ( l≤join to l≤∪
  ; r≤join to r≤∪
  ; least  to ∪-universal
  ) public

private variable x y x′ y′ z : Ob

opaque
  ∪-idem : x ∪ x ＝ x
  ∪-idem = ≤-antisym (∪-universal _ refl refl) l≤∪

  ∪-comm : x ∪ y ＝ y ∪ x
  ∪-comm =
    ≤-antisym
      (∪-universal _ r≤∪ l≤∪)
      (∪-universal _ r≤∪ l≤∪)

  ∪-assoc : x ∪ y ∪ z ＝ (x ∪ y) ∪ z
  ∪-assoc =
    ≤-antisym
      (∪-universal _
        (l≤∪ ∙ l≤∪)
        (∪-universal _ (r≤∪ ∙ l≤∪) r≤∪))
      (∪-universal _
        (∪-universal _ l≤∪ (l≤∪ ∙ r≤∪))
        (r≤∪ ∙ r≤∪))

  ∪-is-semigroup : is-semigroup {A = Ob} _∪_
  ∪-is-semigroup .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = ob-is-set
  ∪-is-semigroup .is-semigroup.assoc _ _ _ = ∪-assoc

  ∪≤∪
    : x ≤ x′
    → y ≤ y′
    → x ∪ y ≤ x′ ∪ y′
  ∪≤∪ p q = ∪-universal _ (p ∙ l≤∪) (q ∙ r≤∪)

  ∪≤∪-l : x ≤ x′ → x ∪ y ≤ x′ ∪ y
  ∪≤∪-l p = ∪≤∪ p refl

  ∪≤∪-r : y ≤ y′ → x ∪ y ≤ x ∪ y′
  ∪≤∪-r p = ∪≤∪ refl p

  ∪→order : x ∪ y ＝ y → x ≤ y
  ∪→order {x} {y} p =
    x      ≤⟨ l≤∪ ⟩
    x ∪ y  =⟨ p ⟩
    y      ∎

  order→∪ : x ≤ y → x ∪ y ＝ y
  order→∪ p = ≤-antisym (∪-universal _ p refl) r≤∪

  ∪≃order : (x ∪ y ＝ y) ≃ (x ≤ y)
  ∪≃order = prop-extₑ! ∪→order order→∪

module _ ⦃ t : Top P ⦄ where opaque
  open Top t

  ∪-absorb-l : ⊤ ∪ x ＝ ⊤
  ∪-absorb-l = ≤-antisym ! l≤∪

  ∪-absorb-r : x ∪ ⊤ ＝ ⊤
  ∪-absorb-r = ≤-antisym ! r≤∪
