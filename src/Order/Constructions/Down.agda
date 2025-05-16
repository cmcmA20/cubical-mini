{-# OPTIONS --safe #-}
module Order.Constructions.Down where

open import Cat.Prelude
open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
import Order.Diagram.Join.Reasoning
import Order.Diagram.Meet.Reasoning

module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P

  record Down (c : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    constructor cut
    field
      {domain} : Ob
      down     : domain ≤ c

  open Down

  unquoteDecl H-Level-Down = declare-record-hlevel 2 H-Level-Down (quote Down)
  unquoteDecl Down-Iso = declare-record-iso Down-Iso (quote Down)

  instance
    Extensional-Down
      : ∀{ℓr} {c} ⦃ eo : Extensional Ob ℓr ⦄
      → Extensional (Down c) ℓr
    Extensional-Down = ≅→extensional Down-Iso (Σ-prop→extensional! auto)

  -- down set aka decategorified slice
  infix 14 _↓
  _↓ : Ob → Poset (o ⊔ ℓ) ℓ
  (c ↓) .Poset.Ob = Down c
  (c ↓) .Poset._≤_ x↓ y↓ = x↓ .domain ≤ y↓ .domain
  (c ↓) .Poset.≤-thin = hlevel 1
  (c ↓) .Poset.≤-refl = refl
  (c ↓) .Poset.≤-trans = _∙_
  (c ↓) .Poset.≤-antisym u v = ext (≤-antisym u v)

  instance
    Down-has-top : {c : Ob} → Top (c ↓)
    Down-has-top .Top.top = cut refl
    Down-has-top .Top.top-is-top = down

    Down-pres-bottom : ⦃ hb : Bottom P ⦄ {c : Ob} → Bottom (c ↓)
    Down-pres-bottom ⦃ hb ⦄ = go where
      open Bottom hb
      go : Bottom _
      go .Bottom.bot = cut ¡
      go .Bottom.bot-is-bot _ = ¡

    Down-pres-joins : ⦃ hj : Has-joins P ⦄ {c : Ob} → Has-joins (c ↓)
    Down-pres-joins ⦃ hj ⦄ {c} {x} {y} = go where
      open Order.Diagram.Join.Reasoning P hj
      go : Join (c ↓) x y
      go .Join.lub = cut (∪-universal c (x .down) (y .down))
      go .Join.has-join .is-join.l≤join = l≤∪
      go .Join.has-join .is-join.r≤join = r≤∪
      go .Join.has-join .is-join.least _ = ∪-universal _

    -- having pullbacks in posets is same as having meets
    Down-pres-meets : ⦃ hm : Has-meets P ⦄ {c : Ob} → Has-meets (c ↓)
    Down-pres-meets ⦃ hm ⦄ {c} {x} {y} = go where
      open Order.Diagram.Meet.Reasoning P hm
      go : Meet (c ↓) _ _
      go .Meet.glb = cut (∩≤r ∙ y .down)
      go .Meet.has-meet .is-meet.meet≤l = ∩≤l
      go .Meet.has-meet .is-meet.meet≤r = ∩≤r
      go .Meet.has-meet .is-meet.greatest _ = ∩-universal _

  ↓-fw : {x y : Ob} → x ≤ y → x ↓ ⇒ y ↓
  ↓-fw x≤y .hom x↓ = cut (x↓ .down ∙ x≤y)
  ↓-fw _   .pres-≤ = refl

  ↓-bw : ⦃ hm : Has-meets P ⦄ {x y : Ob} → y ≤ x → x ↓ ⇒ y ↓
  ↓-bw ⦃ hm ⦄ {x} {y} x≤y = go where
    open Order.Diagram.Meet.Reasoning P hm
    go : x ↓ ⇒ y ↓
    go .hom _ = cut ∩≤r
    go .pres-≤ p = ∩-universal _ (∩≤l ∙ p) ∩≤r

  Forget : {c : Ob} → c ↓ ⇒ P
  Forget .hom = domain
  Forget .pres-≤ = refl

  Δ : {c : Ob} → P ⇒ c ↓
  Δ .hom _ = ⊤ where open Top auto
  Δ .pres-≤ _ = refl
