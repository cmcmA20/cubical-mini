-- open import Cat.Diagram.Product
open import Categories.Prelude

open import Data.Bool

open import Order.Diagram.Glb
open import Order.Base
open import Order.Category

import Order.Reasoning

module Order.Diagram.Meet where

private variable
  o ℓ : Level

record is-meet (P : Poset o ℓ) (a b glb : ⌞ P ⌟) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Poset P
  field
    meet≤l   : glb ≤ a
    meet≤r   : glb ≤ b
    greatest : (lb' : Ob) → lb' ≤ a → lb' ≤ b → lb' ≤ glb

record Meet (P : Poset o ℓ) (a b : ⌞ P ⌟) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    glb : ⌞ P ⌟
    has-meet : is-meet P a b glb
  open is-meet has-meet public

open is-meet

Has-meets : Poset o ℓ → Type (o ⊔ ℓ)
Has-meets P = ∀ x y → Meet P x y

unquoteDecl H-Level-is-meet = declare-record-hlevel 1 H-Level-is-meet (quote is-meet)

module _ {P : Poset o ℓ} where
  open Poset P
  open is-glb
  open Glb

  is-meet→is-glb : ∀ {a b glb} → is-meet P a b glb → is-glb P (if_then a else b) glb
  is-meet→is-glb meet .glb≤fam true = meet .meet≤l
  is-meet→is-glb meet .glb≤fam false = meet .meet≤r
  is-meet→is-glb meet .greatest glb' x = meet .greatest glb' (x true) (x false)

  is-glb→is-meet : ∀ {F : Bool → Ob} {glb} → is-glb P F glb → is-meet P (F true) (F false) glb
  is-glb→is-meet glb .meet≤l = glb .glb≤fam true
  is-glb→is-meet glb .meet≤r = glb .glb≤fam false
  is-glb→is-meet glb .greatest lb' lb'<a lb'<b = glb .greatest lb' λ where
    true  → lb'<a
    false → lb'<b

  meet-unique : ∀ {a b x y} → is-meet P a b x → is-meet P a b y → x ＝ y
  meet-unique {a = a} {b} x-meet y-meet = glb-unique
    (is-meet→is-glb x-meet)
    (is-meet→is-glb y-meet)

  Meet-is-prop : ∀ {a b} → is-prop (Meet P a b)
  Meet-is-prop p q i .Meet.glb =
    meet-unique (Meet.has-meet p) (Meet.has-meet q) i
  Meet-is-prop {a = a} {b = b} p q i .Meet.has-meet =
    is-prop→pathᴾ
      {B = λ i → is-meet P a b (meet-unique (Meet.has-meet p) (Meet.has-meet q) i)}
      (λ i → hlevel 1)
      (Meet.has-meet p) (Meet.has-meet q) i

  instance
    H-Level-Meet
      : ∀ {a b} {n}
      → H-Level (suc n) (Meet P a b)
    H-Level-Meet = hlevel-basic-instance 1 Meet-is-prop

  Meet→Glb : ∀ {a b} → Meet P a b → Glb P (if_then a else b)
  Meet→Glb meet .Glb.glb = Meet.glb meet
  Meet→Glb meet .Glb.has-glb = is-meet→is-glb (Meet.has-meet meet)

  Glb→Meet : ∀ {a b} → Glb P (if_then a else b) → Meet P a b
  Glb→Meet glb .Meet.glb = Glb.glb glb
  Glb→Meet glb .Meet.has-meet = is-glb→is-meet (Glb.has-glb glb)

  is-meet≃is-glb : ∀ {a b glb} → is-equiv (is-meet→is-glb {a} {b} {glb})
  is-meet≃is-glb = biimp-is-equiv! _ is-glb→is-meet

  Meet≃Glb : ∀ {a b} → is-equiv (Meet→Glb {a} {b})
  Meet≃Glb = biimp-is-equiv! _ Glb→Meet

  le→is-meet : ∀ {a b} → a ≤ b → is-meet P a b a
  le→is-meet a≤b .meet≤l = ≤-refl
  le→is-meet a≤b .meet≤r = a≤b
  le→is-meet a≤b .greatest lb' lb'≤a _ = lb'≤a

  le-meet : ∀ {a b l} → a ≤ b → is-meet P a b l → a ＝ l
  le-meet a≤b l = meet-unique (le→is-meet a≤b) l

{-
  open is-product
  open Product

  is-meet→product : ∀ {a b glb : Ob} → is-meet P a b glb → Product (poset→category P) a b
  is-meet→product glb .apex = _
  is-meet→product glb .π₁ = glb .is-meet.meet≤l
  is-meet→product glb .π₂ = glb .is-meet.meet≤r
  is-meet→product glb .has-is-product .⟨_,_⟩ q<a q<b =
    glb .is-meet.greatest _ q<a q<b
  is-meet→product glb .has-is-product .π₁∘⟨⟩ = prop!
  is-meet→product glb .has-is-product .π₂∘⟨⟩ = prop!
  is-meet→product glb .has-is-product .unique _ _ = prop!
-}