{-# OPTIONS --safe #-}
module Order.Constructions.Pointwise where

open import Cat.Prelude
open import Order.Base
open import Order.Constructions.Product
open import Order.Constructions.Props
open import Order.Diagram.Bottom
open import Order.Diagram.Glb
open import Order.Diagram.Join
open import Order.Diagram.Lub
open import Order.Diagram.Meet
open import Order.Diagram.Top

private variable o ℓ o′ ℓ′ ℓᵢ : Level

Pointwise : (I : Type ℓᵢ) (P : I → Poset o ℓ) → Poset (ℓᵢ ⊔ o) (ℓᵢ ⊔ ℓ)
Pointwise I P = po where
  open module P {i} = Poset (P i)
  po : Poset _ _
  po .Poset.Ob = Π[ P ]
  po .Poset._≤_ f g = ∀[ i ꞉ I ] (f i ⇒ g i)
  po .Poset.≤-thin = hlevel 1
  po .Poset.≤-refl = refl
  po .Poset.≤-trans f≤g g≤h = f≤g ∙ g≤h
  po .Poset.≤-antisym f≤g g≤h = ext (λ _ → ≤-antisym f≤g g≤h)

tupleₚ
  : {I : Type ℓᵢ} {P : I → Poset o ℓ} {R : Poset o′ ℓ′}
  → (∀ i → R ⇒ P i)
  → R ⇒ Pointwise I P
tupleₚ f .hom x i = f i # x
tupleₚ f .pres-≤ x≤y = f _ # x≤y

projₚ
  : {I : Type ℓᵢ} {P : I → Poset o ℓ} (i : I)
  → Pointwise I P ⇒ P i
projₚ i .hom f      = f i
projₚ i .pres-≤ f≤g = f≤g

Poset[_,_]
  : (P : Poset o ℓ) (Q : Poset o′ ℓ′)
  → Poset (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) (o ⊔ ℓ′)
Poset[_,_] P Q = po module Poset[_,_] where
  open Poset Q
  po : Poset _ _
  po .Poset.Ob       = P ⇒ Q
  po .Poset._≤_ f g  = Π[ x ꞉ P ] (f # x ≤ g # x)
  po .Poset.≤-thin   = hlevel 1
  po .Poset.≤-refl _ = refl
  po .Poset.≤-trans   f≤g g≤h x = f≤g x ∙ g≤h x
  po .Poset.≤-antisym f≤g g≤f   = ext λ x → ≤-antisym (f≤g x) (g≤f x)
{-# DISPLAY Poset[_,_].po a b = Poset[ a , b ] #-}

instance
  ⇒-Poset-exp : ⇒-notation (Poset o ℓ) (Poset o′ ℓ′) (Poset (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) (o ⊔ ℓ′))
  ⇒-Poset-exp .⇒-notation.Constraint _ _ = ⊤
  ⇒-Poset-exp ._⇒_ P Q = Poset[ P , Q ]

-- FIXME erasure really gets in the way!
module _ {I : Type ℓᵢ} {@0 P : Poset o ℓ} where instance
  Pointwise-pres-bottom : ⦃ b : Bottom P ⦄ → Bottom (Pointwise I λ _ → P)
  Pointwise-pres-bottom ⦃ b ⦄ .Bottom.bot _ = b .Bottom.bot
  Pointwise-pres-bottom ⦃ b ⦄ .Bottom.has-bot _ = b .Bottom.has-bot _

  Pointwise-pres-top : ⦃ t : Top P ⦄ → Top (Pointwise I λ _ → P)
  Pointwise-pres-top ⦃ t ⦄ .Top.top _ = t .Top.top
  Pointwise-pres-top ⦃ t ⦄ .Top.has-top _ = t .Top.has-top _

  Pointwise-pres-joins : ⦃ hj : Has-joins P ⦄ → Has-joins (Pointwise I λ _ → P)
  Pointwise-pres-joins ⦃ hj ⦄ {x = f} {y = g} .Join.lub i = hj {f i} {g i} .Join.lub
  Pointwise-pres-joins ⦃ hj ⦄ .Join.has-join .is-join.l≤join = is-join.l≤join (hj .Join.has-join)
  Pointwise-pres-joins ⦃ hj ⦄ .Join.has-join .is-join.r≤join = is-join.r≤join (hj .Join.has-join)
  Pointwise-pres-joins ⦃ hj ⦄ .Join.has-join .is-join.least _ u v = is-join.least (hj .Join.has-join) _ u v

  Pointwise-pres-meets : ⦃ hm : Has-meets P ⦄ → Has-meets (Pointwise I λ _ → P)
  Pointwise-pres-meets ⦃ hm ⦄ {x = f} {y = g} .Meet.glb i = hm {f i} {g i} .Meet.glb
  Pointwise-pres-meets ⦃ hm ⦄ .Meet.has-meet .is-meet.meet≤l = is-meet.meet≤l (hm .Meet.has-meet)
  Pointwise-pres-meets ⦃ hm ⦄ .Meet.has-meet .is-meet.meet≤r = is-meet.meet≤r (hm .Meet.has-meet)
  Pointwise-pres-meets ⦃ hm ⦄ .Meet.has-meet .is-meet.greatest _ u v = is-meet.greatest (hm .Meet.has-meet) _ u v

  Pointwise-pres-lubs : ⦃ hl : Has-lubs-of-size P ℓ′ ⦄ → Has-lubs-of-size (Pointwise I λ _ → P) ℓ′
  Pointwise-pres-lubs ⦃ hl ⦄ {I = J} {F} .Lub.lub j = hl {I = J} {F = λ k → F k j} .Lub.lub
  Pointwise-pres-lubs ⦃ hl ⦄ .Lub.has-lub .is-lub.fam≤lub j = is-lub.fam≤lub (hl .Lub.has-lub) j
  Pointwise-pres-lubs ⦃ hl ⦄ .Lub.has-lub .is-lub.least _ z = is-lub.least (hl .Lub.has-lub) _ λ j → z j

  Pointwise-pres-glbs : ⦃ hl : Has-glbs-of-size P ℓ′ ⦄ → Has-glbs-of-size (Pointwise I λ _ → P) ℓ′
  Pointwise-pres-glbs ⦃ hl ⦄ {I = J} {F} .Glb.glb j = hl {I = J} {F = λ k → F k j} .Glb.glb
  Pointwise-pres-glbs ⦃ hl ⦄ .Glb.has-glb .is-glb.glb≤fam j = is-glb.glb≤fam (hl .Glb.has-glb) j
  Pointwise-pres-glbs ⦃ hl ⦄ .Glb.has-glb .is-glb.greatest _ z = is-glb.greatest (hl .Glb.has-glb) _ λ j → z j
