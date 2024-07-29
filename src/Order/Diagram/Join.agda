--open import Cat.Diagram.Coproduct
open import Categories.Prelude

open import Data.Bool

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category

import Order.Reasoning

module Order.Diagram.Join where

private variable
  o ℓ : Level

record is-join (P : Poset o ℓ) (a b lub : ⌞ P ⌟) : 𝒰 (o ⊔ ℓ) where
  no-eta-equality
  open Poset P

  field
    l≤join : a ≤ lub
    r≤join : b ≤ lub
    least  : (ub' : Ob) → a ≤ ub' → b ≤ ub' → lub ≤ ub'

record Join (P : Poset o ℓ) (a b : ⌞ P ⌟) : 𝒰 (o ⊔ ℓ) where
  no-eta-equality
  field
    lub : ⌞ P ⌟
    has-join : is-join P a b lub
  open is-join has-join public

Has-joins : Poset o ℓ → Type (o ⊔ ℓ)
Has-joins P = ∀ x y → Join P x y

open is-join

unquoteDecl H-Level-is-join = declare-record-hlevel 1 H-Level-is-join (quote is-join)

module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P
  open is-lub
  open Lub

  is-join→is-lub : ∀ {a b lub} → is-join P a b lub → is-lub P (if_then a else b) lub
  is-join→is-lub join .fam≤lub true = join .l≤join
  is-join→is-lub join .fam≤lub false = join .r≤join
  is-join→is-lub join .least ub' x = join .least ub' (x true) (x false)

  is-lub→is-join : ∀ {a b lub} → is-lub P (if_then a else b) lub → is-join P a b lub
  is-lub→is-join lub .l≤join = lub .fam≤lub true
  is-lub→is-join lub .r≤join = lub .fam≤lub false
  is-lub→is-join lub .least ub' a<ub' b<ub' = lub .least ub' λ where
    true  → a<ub'
    false → b<ub'

  join-unique
    : ∀ {a b x y}
    → is-join P a b x → is-join P a b y
    → x ＝ y
  join-unique {a} {b} {x} {y} p q =
    lub-unique (is-join→is-lub p) (is-join→is-lub q)

  Join-is-prop : ∀ {a b} → is-prop (Join P a b)
  Join-is-prop p q i .Join.lub =
    join-unique (Join.has-join p) (Join.has-join q) i
  Join-is-prop {a = a} {b = b} p q i .Join.has-join =
    is-prop→pathᴾ {B = λ i → is-join P a b (join-unique (Join.has-join p) (Join.has-join q) i)}
      (λ i → hlevel 1)
      (Join.has-join p) (Join.has-join q) i

  instance
    H-Level-Join
      : ∀ {a b} {n}
      → H-Level (suc n) (Join P a b)
    H-Level-Join = hlevel-basic-instance 1 Join-is-prop

  Join→Lub : ∀ {a b} → Join P a b → Lub P (if_then a else b)
  Join→Lub join .Lub.lub = Join.lub join
  Join→Lub join .Lub.has-lub = is-join→is-lub (Join.has-join join)

  Lub→Join : ∀ {a b} → Lub P (if_then a else b) → Join P a b
  Lub→Join lub .Join.lub = Lub.lub lub
  Lub→Join lub .Join.has-join = is-lub→is-join (Lub.has-lub lub)

  is-join≃is-lub : ∀ {a b lub : Ob} → is-equiv (is-join→is-lub {a} {b} {lub})
  is-join≃is-lub = biimp-is-equiv! _ is-lub→is-join

  Join≃Lub : ∀ {a b} → is-equiv (Join→Lub {a} {b})
  Join≃Lub = biimp-is-equiv! _ Lub→Join

  gt→is-join : ∀ {a b} → a ≤ b → is-join P a b b
  gt→is-join a≤b .l≤join = a≤b
  gt→is-join a≤b .r≤join = ≤-refl
  gt→is-join a≤b .least ub' _ b≤ub' = b≤ub'

  gt-join : ∀ {a b l} → a ≤ b → is-join P a b l → b ＝ l
  gt-join a≤b l = join-unique (gt→is-join a≤b) l

{-
  open is-coproduct
  open Coproduct

  is-join→coproduct : ∀ {a b lub : Ob} → is-join P a b lub → Coproduct (poset→category P) a b
  is-join→coproduct lub .coapex = _
  is-join→coproduct lub .ι₁ = lub .is-join.l≤join
  is-join→coproduct lub .ι₂ = lub .is-join.r≤join
  is-join→coproduct lub .has-is-coproduct .[_,_] a<q b<q =
    lub .is-join.least _ a<q b<q
  is-join→coproduct lub .has-is-coproduct .[]∘ι₁ = prop!
  is-join→coproduct lub .has-is-coproduct .[]∘ι₂ = prop!
  is-join→coproduct lub .has-is-coproduct .unique _ _ = prop!
-}
