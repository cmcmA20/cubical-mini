{-# OPTIONS --safe #-}
module Order.Diagram.Join where

open import Cat.Prelude
open import Cat.Diagram.Coproduct

open import Order.Base
open import Order.Category
open import Order.Diagram.Lub

open import Data.Bool

private variable o ℓ : Level

module _ (P : Poset o ℓ) (a b : ⌞ P ⌟) where
  open Poset P

  record is-join (lub : Ob) : 𝒰 (o ⊔ ℓ) where
    no-eta-equality
    field
      l≤join : a ≤ lub
      r≤join : b ≤ lub
      least  : (ub′ : Ob) → a ≤ ub′ → b ≤ ub′ → lub ≤ ub′

  record Join : 𝒰 (o ⊔ ℓ) where
    no-eta-equality
    field
      lub      : Ob
      has-join : is-join lub
    open is-join has-join public

unquoteDecl H-Level-is-join = declare-record-hlevel 1 H-Level-is-join (quote is-join)
unquoteDecl Join-Iso = declare-record-iso Join-Iso (quote Join)

Has-joins : Poset o ℓ → Type (o ⊔ ℓ)
Has-joins P = ∀{x y} → Join P x y

module _ {P : Poset o ℓ} {a b : ⌞ P ⌟} where
  open Poset P
  open is-lub
  open is-join
  open Join

  private variable x y l : Ob

  is-join→is-lub : is-join P a b l → is-lub P (if_then a else b) l
  is-join→is-lub join .fam≤lub true = join .l≤join
  is-join→is-lub join .fam≤lub false = join .r≤join
  is-join→is-lub join .least ub′ x = join .least ub′ (x true) (x false)

  is-lub→is-join : is-lub P (if_then a else b) l → is-join P a b l
  is-lub→is-join lub .l≤join = lub .fam≤lub true
  is-lub→is-join lub .r≤join = lub .fam≤lub false
  is-lub→is-join lub .least ub′ a<ub′ b<ub′ = lub .least ub′ λ where
    true  → a<ub′
    false → b<ub′

  is-join≃is-lub : is-join P a b l ≃ is-lub P (if_then a else b) l
  is-join≃is-lub = is-join→is-lub , biimp-is-equiv! _ is-lub→is-join

  join-unique : is-join P a b x → is-join P a b y → x ＝ y
  join-unique {x} {y} p q =
    lub-unique (is-join→is-lub p) (is-join→is-lub q)

  Join-is-prop : is-prop (Join P a b)
  Join-is-prop = ≅→is-of-hlevel 1 Join-Iso λ x y → join-unique (x .snd) (y .snd) ,ₚ prop!

  instance opaque
    H-Level-Join
      : ∀ {n} ⦃ _ : 1 ≤ʰ n ⦄
      → H-Level n (Join P a b)
    H-Level-Join ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 Join-is-prop

  Join→Lub : Join P a b → Lub P (if_then a else b)
  Join→Lub join .Lub.lub = Join.lub join
  Join→Lub join .Lub.has-lub = is-join→is-lub (Join.has-join join)

  Lub→Join : Lub P (if_then a else b) → Join P a b
  Lub→Join lub .Join.lub = Lub.lub lub
  Lub→Join lub .Join.has-join = is-lub→is-join (Lub.has-lub lub)

  Join≃Lub : Join P a b ≃ Lub P (if_then a else b)
  Join≃Lub = Join→Lub , biimp-is-equiv! _ Lub→Join

  gt→is-join : a ≤ b → is-join P a b b
  gt→is-join a≤b .l≤join = a≤b
  gt→is-join a≤b .r≤join = ≤-refl
  gt→is-join a≤b .least ub′ _ b≤ub′ = b≤ub′

  gt-join : ∀ {l} → a ≤ b → is-join P a b l → b ＝ l
  gt-join a≤b l = join-unique (gt→is-join a≤b) l

  =→is-join : y ＝ x → is-join P a b y → is-join P a b x
  =→is-join p j .l≤join = subst (a ≤_) p (j .l≤join)
  =→is-join p j .r≤join = subst (b ≤_) p (j .r≤join)
  =→is-join p j .least ub′ a≤ub′ b≤ub′ = subst (_≤ ub′) p (j .least ub′ a≤ub′ b≤ub′)

  =→join : (m : Join P a b) → m .lub ＝ x → Join P a b
  =→join {x} j p .lub = x
  =→join j p .has-join = =→is-join p (j .has-join)

  open is-coproduct
  open Coproduct

  join→coproduct : Join P a b → Coproduct (poset→precategory P) a b
  join→coproduct j .coapex = _
  join→coproduct j .ι₁ = j .l≤join
  join→coproduct j .ι₂ = j .r≤join
  join→coproduct j .has-is-coproduct .[_,_]₊ = j .has-join .least _
  join→coproduct j .has-is-coproduct .[]∘ι₁ = prop!
  join→coproduct j .has-is-coproduct .[]∘ι₂ = prop!
  join→coproduct j .has-is-coproduct .unique _ _ = prop!
