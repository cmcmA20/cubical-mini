{-# OPTIONS --safe #-}
module Order.Base where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel

open import Structures.IdentitySystem

private variable n : HLevel

record is-partial-order {ℓ ℓ′} {A : Type ℓ}
          (_≤_ : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    ≤-thin    : ∀ {x y} → is-prop (x ≤ y)
    ≤-refl    : ∀ {x} → x ≤ x
    ≤-trans   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ＝ y

  instance
    H-Level-≤-prop : ∀ {x y} → H-Level (suc n) (x ≤ y)
    H-Level-≤-prop = hlevel-prop-instance ≤-thin

  has-is-set : is-set A
  has-is-set = identity-system→is-of-hlevel 1
    {r = λ _ → ≤-refl , ≤-refl}
    (set-identity-system hlevel! (≤-antisym $²_))
    hlevel!

  instance
    H-Level-po-carrier : H-Level (2 + n) A
    H-Level-po-carrier = hlevel-basic-instance 2 has-is-set


unquoteDecl is-partial-order-iso = declare-record-iso is-partial-order-iso (quote is-partial-order)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  R : A → A → Type ℓ′

instance
  H-Level-is-partial-order : ∀ {n} → H-Level (suc n) (is-partial-order R)
  H-Level-is-partial-order = hlevel-prop-instance $ is-prop-η λ x →
    let open is-partial-order x in is-prop-β (iso→is-of-hlevel 1 is-partial-order-iso hlevel!) x


record Poset-on {ℓ} ℓ′ (A : Type ℓ) : Type (ℓ ⊔ ℓsuc ℓ′) where
  no-eta-equality
  field
    _≤_          : A → A → Type ℓ′
    has-is-poset : is-partial-order _≤_
  open is-partial-order has-is-poset public

-- record make-poset {ℓ} ℓ′ (A : Type ℓ) : Type (ℓ ⊔ ℓsuc ℓ′) where
--   no-eta-equality

--   field
--     rel     : A → A → Type ℓ′
--     id      : ∀ {x} → rel x x
--     thin    : ∀ {x y} → is-prop (rel x y)
--     trans   : ∀ {x y z} → rel x y → rel y z → rel x z
--     antisym : ∀ {x y} → rel x y → rel y x → x ＝ y

--   to-poset-on : Poset-on ℓ′ A
--   to-poset-on .Poset-on._≤_ = rel
--   to-poset-on .Poset-on.has-is-poset .is-partial-order.≤-thin = thin
--   to-poset-on .Poset-on.has-is-poset .is-partial-order.≤-refl = id
--   to-poset-on .Poset-on.has-is-poset .is-partial-order.≤-trans = trans
--   to-poset-on .Poset-on.has-is-poset .is-partial-order.≤-antisym = antisym

-- to-poset : ∀ {ℓ ℓ′} (A : Type ℓ) → make-poset ℓ′ A → Poset ℓ ℓ′
-- ∣ to-poset A mk .fst ∣ = A
-- to-poset A mk .fst .is-tr = Poset-on.has-is-set (make-poset.to-poset-on mk)
-- to-poset A mk .snd = make-poset.to-poset-on mk
