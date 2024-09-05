{-# OPTIONS --safe #-}
module Order.Constructions.Props where

open import Cat.Prelude
open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Glb
open import Order.Diagram.Join
open import Order.Diagram.Lub
open import Order.Diagram.Meet
open import Order.Diagram.Top

open import Data.Sum

private variable ℓ : Level

-- TODO maybe make antisymmetry erased?
@0 Props : (ℓ : Level) → Poset (ℓsuc ℓ) ℓ
Props ℓ .Poset.Ob = Prop ℓ
Props _ .Poset._≤_ P Q = ⌞ P ⇒ Q ⌟
Props _ .Poset.≤-thin = hlevel 1
Props _ .Poset.≤-refl = refl
Props _ .Poset.≤-trans = _∙_
Props _ .Poset.≤-antisym f g = ext (f , g)

instance
  Props-has-bot : Bottom (Props ℓ)
  Props-has-bot .Bottom.bot = ⊥
  Props-has-bot .Bottom.has-bot _ ()

  Props-has-top : Top (Props ℓ)
  Props-has-top .Top.top = ⊤
  Props-has-top .Top.has-top _ _ = lift tt

  Props-has-joins : Has-joins (Props ℓ)
  Props-has-joins {x = P} {y = Q} .Join.lub = P ⊎₁ Q
  Props-has-joins .Join.has-join .is-join.l≤join p = ∣ inl p ∣₁
  Props-has-joins .Join.has-join .is-join.r≤join p = ∣ inr p ∣₁
  Props-has-joins .Join.has-join .is-join.least R p→r q→r =
    ∥-∥₁.elim (λ _ → R .n-Type.carrier-is-tr) [ p→r , q→r ]ᵤ -- FIXME hlevel search tries to use erased instance

  Props-has-meets : Has-meets (Props ℓ)
  Props-has-meets {x = P} {y = Q} .Meet.glb = P × Q
  Props-has-meets .Meet.has-meet .is-meet.meet≤l = fst
  Props-has-meets .Meet.has-meet .is-meet.meet≤r = snd
  Props-has-meets .Meet.has-meet .is-meet.greatest R r→p r→q r = r→p r , r→q r

  Props-has-lubs : Has-lubs-of-size (Props ℓ) ℓ
  Props-has-lubs {I} {F} .Lub.lub = ∃[ i ꞉ I ] F i
  Props-has-lubs .Lub.has-lub .is-lub.fam≤lub i fi = ∣ i , fi ∣₁
  Props-has-lubs .Lub.has-lub .is-lub.least R f =
    ∥-∥₁.elim (λ _ → R .n-Type.carrier-is-tr) (f $ₜ²_)

  Props-has-glbs : Has-glbs-of-size (Props ℓ) ℓ
  Props-has-glbs {I} {F} .Glb.glb = Π[ i ꞉ I ] F i
  Props-has-glbs .Glb.has-glb .is-glb.glb≤fam i fi = fi i
  Props-has-glbs .Glb.has-glb .is-glb.greatest R f r i = f i r
