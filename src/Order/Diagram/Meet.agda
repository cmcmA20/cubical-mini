{-# OPTIONS --safe #-}
module Order.Diagram.Meet where

open import Cat.Prelude
open import Cat.Diagram.Product

open import Order.Base
open import Order.Category
open import Order.Diagram.Glb

open import Data.Bool

private variable
  o ℓ : Level
  n : HLevel

module _ (P : Poset o ℓ) (a b : ⌞ P ⌟) where
  open Poset P

  record is-meet (glb : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      meet≤l   : glb ≤ a
      meet≤r   : glb ≤ b
      greatest : (lb′ : Ob) → lb′ ≤ a → lb′ ≤ b → lb′ ≤ glb

  record Meet : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      glb      : Ob
      has-meet : is-meet glb
    open is-meet has-meet public

unquoteDecl H-Level-is-meet = declare-record-hlevel 1 H-Level-is-meet (quote is-meet)
unquoteDecl Meet-Iso = declare-record-iso Meet-Iso (quote Meet)

Has-meets : Poset o ℓ → Type (o ⊔ ℓ)
Has-meets P = ∀{x y} → Meet P x y

module _ {P : Poset o ℓ} {a b : ⌞ P ⌟} where
  open Poset P
  open is-glb
  open is-meet
  open Meet

  private variable x y g l : Ob

  is-meet→is-glb : is-meet P a b g → is-glb P (if_then a else b) g
  is-meet→is-glb meet .glb≤fam true = meet .meet≤l
  is-meet→is-glb meet .glb≤fam false = meet .meet≤r
  is-meet→is-glb meet .greatest glb′ x = meet .greatest glb′ (x true) (x false)

  is-glb→is-meet : ∀ {F : Bool → Ob} → is-glb P F g → is-meet P (F true) (F false) g
  is-glb→is-meet glb .meet≤l = glb .glb≤fam true
  is-glb→is-meet glb .meet≤r = glb .glb≤fam false
  is-glb→is-meet glb .greatest lb′ lb′<a lb′<b = glb .greatest lb′ λ where
    true  → lb′<a
    false → lb′<b

  is-meet≃is-glb : is-meet P a b g ≃ is-glb P (if_then a else b) g
  is-meet≃is-glb = is-meet→is-glb , biimp-is-equiv! _ is-glb→is-meet

  meet-unique : is-meet P a b x → is-meet P a b y → x ＝ y
  meet-unique x-meet y-meet = glb-unique
    (is-meet→is-glb x-meet)
    (is-meet→is-glb y-meet)

  Meet-is-prop : is-prop (Meet P a b)
  Meet-is-prop = ≅→is-of-hlevel 1 Meet-Iso λ x y → meet-unique (x .snd) (y .snd) ,ₚ prop!

  instance opaque
    H-Level-Meet : ⦃ _ : 1 ≤ʰ n ⦄ → H-Level n (Meet P a b)
    H-Level-Meet ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 Meet-is-prop

  Meet→Glb : Meet P a b → Glb P (if_then a else b)
  Meet→Glb m .Glb.glb = m .glb
  Meet→Glb m .Glb.has-glb = is-meet→is-glb (m .has-meet)

  Glb→Meet : Glb P (if_then a else b) → Meet P a b
  Glb→Meet glb .glb = Glb.glb glb
  Glb→Meet glb .has-meet = is-glb→is-meet (Glb.has-glb glb)

  Meet≃Glb : Meet P a b ≃ Glb P (if_then a else b)
  Meet≃Glb = Meet→Glb , biimp-is-equiv! _ Glb→Meet

  le→is-meet : a ≤ b → is-meet P a b a
  le→is-meet a≤b .meet≤l = ≤-refl
  le→is-meet a≤b .meet≤r = a≤b
  le→is-meet a≤b .greatest lb′ lb′≤a _ = lb′≤a

  le-meet : a ≤ b → is-meet P a b l → a ＝ l
  le-meet a≤b l = meet-unique (le→is-meet a≤b) l

  =→is-meet : y ＝ x → is-meet P a b y → is-meet P a b x
  =→is-meet p m .meet≤l = subst (_≤ a) p (m .meet≤l)
  =→is-meet p m .meet≤r = subst (_≤ b) p (m .meet≤r)
  =→is-meet p m .greatest lb′ lb′≤a lb′≤b = subst (lb′ ≤_) p (m .greatest lb′ lb′≤a lb′≤b)

  =→meet : (m : Meet P a b) → m .glb ＝ x → Meet P a b
  =→meet {x} m p .glb = x
  =→meet m p .has-meet = =→is-meet p (m .has-meet)

  open is-product
  open Product

  meet→product : Meet P a b → Product (poset→precategory P) a b
  meet→product m .apex = _
  meet→product m .π₁ = m .has-meet .meet≤l
  meet→product m .π₂ = m .has-meet .meet≤r
  meet→product m .has-is-product .⟨_,_⟩ₓ = m .has-meet .greatest _
  meet→product m .has-is-product .π₁∘⟨⟩ = prop!
  meet→product m .has-is-product .π₂∘⟨⟩ = prop!
  meet→product m .has-is-product .unique _ _ = prop!
