{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Lub

module Order.Diagram.Lub.Reasoning
  {o ℓ} (P : Poset o ℓ) {ℓ′} (hl : Has-lubs-of-size P ℓ′)
  where

open import Algebra.Monoid.Commutative
open import Categories.Prelude

open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Reasoning P

open import Data.Bool as Bool

lubs : {I : Type ℓ′} (F : I → Ob) → Lub P F
lubs F = hl {F = F}

⨆ : {I : Type ℓ′} (F : I → Ob) → Ob
⨆ F = lubs F .Lub.lub

module lubs {I} {F} = Lub (lubs {I} F)
open lubs renaming
  ( fam≤lub to fam≤⨆
  ; least   to ⨆-universal
  ) public

Bottom-Poset-Lub : Bottom P
Bottom-Poset-Lub .Bottom.bot = ⨆ {I = Lift ℓ′ ⊥} λ()
Bottom-Poset-Lub .Bottom.has-bot _ = ⨆-universal _ λ ()

Join-Poset-Lub : Has-joins P
Join-Poset-Lub {x} {y} .Join.lub = ⨆ {I = Lift ℓ′ Bool} (rec! (if_then x else y))
Join-Poset-Lub .Join.has-join .is-join.l≤join = fam≤⨆ (lift true)
Join-Poset-Lub .Join.has-join .is-join.r≤join = fam≤⨆ (lift false)
Join-Poset-Lub .Join.has-join .is-join.least ub′ p q = ⨆-universal _ (elim! (Bool.elim p q))

open Bottom Bottom-Poset-Lub public
open import Order.Diagram.Join.Reasoning P Join-Poset-Lub public

opaque
  ∪-id-l : {x : Ob} → ⊥ ∪ x ＝ x
  ∪-id-l {x} = ≤-antisym
    (∪-universal _ (⨆-universal _ λ ()) refl)
    r≤∪

  ∪-id-r : {x : Ob} → x ∪ ⊥ ＝ x
  ∪-id-r {x} = ≤-antisym
    (∪-universal _ refl (⨆-universal _ λ ()))
    l≤∪

  ∪-is-comm-monoid : is-comm-monoid {A = Ob} _∪_
  ∪-is-comm-monoid = to-is-comm-monoid go where
    open make-comm-monoid
    go : make-comm-monoid Ob
    go .monoid-is-set = ob-is-set
    go .id = ⊥
    go ._⋆_ = _∪_
    go .id-l _ = ∪-id-l
    go .id-r _ = ∪-id-r
    go .assoc _ _ _ = ∪-assoc
    go .comm _ _ = ∪-comm
