{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Glb

module Order.Diagram.Glb.Reasoning
  {o ℓ} (P : Poset o ℓ) {ℓ′} (hl : Has-glbs-of-size P ℓ′)
  where

open import Algebra.Monoid.Commutative
open import Categories.Prelude

open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Reasoning P

open import Data.Bool as Bool

glbs : {I : Type ℓ′} (F : I → Ob) → Glb P F
glbs F = hl {F = F}

⨅ : {I : Type ℓ′} (F : I → Ob) → Ob
⨅ F = glbs F .Glb.glb

module glbs {I} {F} = Glb (glbs {I} F)
open glbs renaming
  ( glb≤fam  to ⨅≤fam
  ; greatest to ⨅-universal
  ) public

Top-Poset-Lub : Top P
Top-Poset-Lub .Top.top = ⨅ {I = Lift ℓ′ ⊥} λ()
Top-Poset-Lub .Top.has-top _ = ⨅-universal _ λ ()

Meet-Poset-Glb : Has-meets P
Meet-Poset-Glb {x} {y} .Meet.glb = ⨅ {I = Lift ℓ′ Bool} (rec! (if_then x else y))
Meet-Poset-Glb .Meet.has-meet .is-meet.meet≤l = ⨅≤fam (lift true)
Meet-Poset-Glb .Meet.has-meet .is-meet.meet≤r = ⨅≤fam (lift false)
Meet-Poset-Glb .Meet.has-meet .is-meet.greatest ub′ p q = ⨅-universal _ (elim! (Bool.elim p q))

open Top Top-Poset-Lub public
open import Order.Diagram.Meet.Reasoning P Meet-Poset-Glb public

opaque
  ∩-id-l : {x : Ob} → ⊤ ∩ x ＝ x
  ∩-id-l {x} = ≤-antisym
    ∩≤r
    (∩-universal _ (⨅-universal _ λ ()) refl)

  ∩-id-r : {x : Ob} → x ∩ ⊤ ＝ x
  ∩-id-r {x} = ≤-antisym
    ∩≤l
    (∩-universal _ refl (⨅-universal _ λ ()))

  ∩-is-comm-monoid : is-comm-monoid {A = Ob} _∩_
  ∩-is-comm-monoid = to-is-comm-monoid go where
    open make-comm-monoid
    go : make-comm-monoid Ob
    go .monoid-is-set = ob-is-set
    go .id = ⊤
    go ._⋆_ = _∩_
    go .id-l _ = ∩-id-l
    go .id-r _ = ∩-id-r
    go .assoc _ _ _ = ∩-assoc
    go .comm _ _ = ∩-comm
