{-# OPTIONS --safe #-}
module Order.Base where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel

open import Structures.IdentitySystem


record is-partial-order {ℓ ℓ′} {A : Type ℓ}
          (_≤_ : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    instance ≤-thin : ∀ {x y} → is-prop (x ≤ y)
    ≤-refl    : ∀ {x} → x ≤ x
    ≤-trans   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ＝ y

  instance
    has-is-set : is-set A
    has-is-set = identity-system→hlevel 1
      {r = λ _ → ≤-refl , ≤-refl}
      (set-identity-system hlevel! (≤-antisym $²_))
      hlevel!


private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  R : A → A → Type ℓ′

is-partial-order-is-of-hlevel : ∀ n → is-of-hlevel (suc n) (is-partial-order R)
is-partial-order-is-of-hlevel n = is-of-hlevel-+-left 1 _ is-partial-order-is-prop where
  private unquoteDecl eqv = declare-record-iso eqv (quote is-partial-order)
  is-partial-order-is-prop : is-prop (is-partial-order R)
  is-partial-order-is-prop = is-prop-η λ x y →
    let open is-partial-order x in is-prop-β (iso→is-of-hlevel 1 eqv hlevel!) x y

instance
  decomp-hlevel-po
    : goal-decomposition (quote is-of-hlevel) (is-partial-order R)
  decomp-hlevel-po = decomp (quote is-partial-order-is-of-hlevel) (`level-minus 1 ∷ [])


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
