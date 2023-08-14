{-# OPTIONS --safe #-}
module Order.Total where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel

open import Structures.IdentitySystem

open import Order.Base

open import Data.Sum.Base

open import Truncation.Propositional.Base


record is-total-order {ℓ ℓ′} {A : Type ℓ}
          (_≤_ : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    has-partial-order : is-partial-order _≤_
    ≤-total : ∀ {x y} → x ≤ y ⊎₁ y ≤ x
  open is-partial-order has-partial-order public


private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  R : A → A → Type ℓ′

is-total-order-is-of-hlevel : ∀ n → is-of-hlevel (suc n) (is-total-order R)
is-total-order-is-of-hlevel n = is-of-hlevel-+-left 1 _ is-total-order-is-prop where
  private unquoteDecl eqv = declare-record-iso eqv (quote is-total-order)
  is-total-order-is-prop : is-prop (is-total-order R)
  is-total-order-is-prop = is-prop-η λ x y → let open is-total-order x in
    is-prop-β (iso→is-of-hlevel 1 eqv hlevel!) x y

instance
  decomp-hlevel-to
    : goal-decomposition (quote is-of-hlevel) (is-total-order R)
  decomp-hlevel-to = decomp (quote is-total-order-is-of-hlevel) (`level-minus 1 ∷ [])
