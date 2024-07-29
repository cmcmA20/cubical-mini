open import Algebra.Semigroup
open import Algebra.Magma

open import Categories.Prelude

open import Order.Diagram.Join
open import Order.Base

import Order.Reasoning

module Order.Diagram.Join.Reasoning
  {o ℓ} {P : Poset o ℓ} {_∪_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟}
  (∪-joins : ∀ x y → is-join P x y (x ∪ y))
  where

open Order.Reasoning P
open Join

joins : ∀ x y → Join P x y
joins x y .lub      = x ∪ y
joins x y .has-join = ∪-joins x y

module joins {x} {y} = Join (joins x y)
open joins renaming
  ( l≤join to l≤∪
  ; r≤join to r≤∪
  ; least to ∪-universal)
  public

abstract
  ∪-idem : ∀ {x} → x ∪ x ＝ x
  ∪-idem = ≤-antisym (∪-universal _ ≤-refl ≤-refl) l≤∪

  ∪-comm : ∀ {x y} → x ∪ y ＝ y ∪ x
  ∪-comm =
    ≤-antisym
      (∪-universal _ r≤∪ l≤∪)
      (∪-universal _ r≤∪ l≤∪)

  ∪-assoc : ∀ {x y z} → x ∪ (y ∪ z) ＝ (x ∪ y) ∪ z
  ∪-assoc =
    ≤-antisym
      (∪-universal _
        (≤-trans l≤∪ l≤∪)
        (∪-universal _ (≤-trans r≤∪ l≤∪) r≤∪))
      (∪-universal _
        (∪-universal _ l≤∪ (≤-trans l≤∪ r≤∪))
        (≤-trans r≤∪ r≤∪))

  ∪-is-semigroup : is-semigroup _∪_
  ∪-is-semigroup .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = ob-is-set
  ∪-is-semigroup .is-semigroup.assoc _ _ _ = ∪-assoc

  ∪≤∪
    : ∀ {x y x' y'}
    → x ≤ x'
    → y ≤ y'
    → (x ∪ y) ≤ (x' ∪ y')
  ∪≤∪ p q = ∪-universal _ (≤-trans p l≤∪) (≤-trans q r≤∪)

  ∪≤∪l : ∀ {x y x'} → x ≤ x' → (x ∪ y) ≤ (x' ∪ y)
  ∪≤∪l p = ∪≤∪ p ≤-refl

  ∪≤∪r : ∀ {x y y'} → y ≤ y' → (x ∪ y) ≤ (x ∪ y')
  ∪≤∪r p = ∪≤∪ ≤-refl p

  ∪→order : ∀ {x y} → x ∪ y ＝ y → x ≤ y
  ∪→order {x} {y} p =
    x       ≤⟨ l≤∪ ⟩
    (x ∪ y) =⟨ p ⟩
    y       ∎

  order→∪ : ∀ {x y} → x ≤ y → x ∪ y ＝ y
  order→∪ p = ≤-antisym (∪-universal _ p ≤-refl) r≤∪

  ∪≃order : ∀ {x y} → (x ∪ y ＝ y) ≃ (x ≤ y)
  ∪≃order = prop-extₑ! ∪→order order→∪

