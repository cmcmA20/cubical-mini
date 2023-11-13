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

unquoteDecl is-total-order-iso = declare-record-iso is-total-order-iso (quote is-total-order)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  R : A → A → Type ℓ′

instance
  H-Level-is-total-order : ∀ {n} → H-Level (suc n) (is-total-order R)
  H-Level-is-total-order = hlevel-prop-instance $
    is-of-hlevel-≃ 1 (iso→equiv is-total-order-iso) hlevel!
