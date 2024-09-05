{-# OPTIONS --safe #-}
module Order.Constructions.Lower where

open import Cat.Prelude
open import Order.Base
open import Order.Constructions.Pointwise
open import Order.Constructions.Product
open import Order.Constructions.Props
open import Order.Diagram.Bottom
open import Order.Diagram.Glb
open import Order.Diagram.Join
open import Order.Diagram.Lub
open import Order.Diagram.Meet
open import Order.Diagram.Top
import Order.Reasoning

open import Data.Sum

private variable o ℓ ℓ′ : Level

module @0 _ (P : Poset o ℓ) (ℓ′ : Level) where
  Lower-sets : Poset (o ⊔ ℓ ⊔ ℓsuc ℓ′) (o ⊔ ℓ′)
  Lower-sets = P ᵒᵖ ⇒ Props ℓ′

  Lower-set : Type (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  Lower-set = ⌞ Lower-sets ⌟

module _ {P : Poset o ℓ} where
  open Order.Reasoning P

  infix 11 _⇓
  _⇓ : Ob → Lower-set P ℓ
  (x ⇓) .hom y = el! (y ≤ x)
  (x ⇓) .pres-≤ = _∙_

  よₚ : P ⇒ Lower-sets P ℓ
  よₚ .hom = _⇓
  よₚ .pres-≤ p _ q = q ∙ p

  instance
    Lower-sets-bottom : Bottom (Lower-sets P ℓ′)
    Lower-sets-bottom .Bottom.bot .hom _ = ⊥

    Lower-sets-top : Top (Lower-sets P ℓ′)
    Lower-sets-top .Top.top .hom _ = ⊤
    Lower-sets-top .Top.top .pres-≤ = _
    Lower-sets-top .Top.has-top = _

    @0 Lower-sets-have-joins : Has-joins (Lower-sets P ℓ′)
    Lower-sets-have-joins {x = A} {y = B} .Join.lub .hom t = A # t ⊎₁ B # t
    Lower-sets-have-joins {x = A} {y = B} .Join.lub .pres-≤ p = map [ A # p ∙ inl , B # p ∙ inr ]ᵤ
    Lower-sets-have-joins .Join.has-join .is-join.l≤join x x∈A = ∣ inl x∈A ∣₁
    Lower-sets-have-joins .Join.has-join .is-join.r≤join x x∈B = ∣ inr x∈B ∣₁
    Lower-sets-have-joins .Join.has-join .is-join.least _ f g x = rec! [ f x , g x ]ᵤ

    @0 Lower-sets-have-meets : Has-meets (Lower-sets P ℓ′)
    Lower-sets-have-meets {x = A} {y = B} .Meet.glb .hom t = A # t × B # t
    Lower-sets-have-meets {x = A} {y = B} .Meet.glb .pres-≤ p = bimap (A # p) (B # p)
    Lower-sets-have-meets .Meet.has-meet .is-meet.meet≤l _ = fst
    Lower-sets-have-meets .Meet.has-meet .is-meet.meet≤r _ = snd
    Lower-sets-have-meets .Meet.has-meet .is-meet.greatest _ f g x p = f x p , g x p

    @0 Lower-sets-have-lubs : Has-lubs-of-size (Lower-sets P ℓ′) ℓ′
    Lower-sets-have-lubs {I} {F} .Lub.lub .hom i = el! (∃[ j ꞉ I ] i ∈ (F j $_))
    Lower-sets-have-lubs {F} .Lub.lub .pres-≤ y≤x = map (second λ {i} → F i # y≤x)
    Lower-sets-have-lubs .Lub.has-lub .is-lub.fam≤lub i _ z = ∣ i , z ∣₁
    Lower-sets-have-lubs .Lub.has-lub .is-lub.least x f y = rec! λ z → f z y

    @0 Lower-sets-have-glbs : Has-glbs-of-size (Lower-sets P ℓ′) ℓ′
    Lower-sets-have-glbs {I} {F} .Glb.glb .hom i = el! (Π[ j ꞉ I ] i ∈ (F j $_))
    Lower-sets-have-glbs {F} .Glb.glb .pres-≤ y≤x f j = (F j # y≤x) $ f j
    Lower-sets-have-glbs .Glb.has-glb .is-glb.glb≤fam i _ f = f i
    Lower-sets-have-glbs .Glb.has-glb .is-glb.greatest _ f x w i = f i x w
