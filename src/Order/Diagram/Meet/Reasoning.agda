open import Algebra.Semigroup
open import Algebra.Magma

open import Categories.Prelude

open import Order.Diagram.Meet
open import Order.Base
import Order.Reasoning

module Order.Diagram.Meet.Reasoning
  {o ℓ} {P : Poset o ℓ} {_∩_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟}
  (∩-meets : ∀ x y → is-meet P x y (x ∩ y))
  where

open Order.Reasoning P
open Meet

meets : ∀ x y → Meet P x y
meets x y .glb      = x ∩ y
meets x y .has-meet = ∩-meets x y

module meets {x} {y} = Meet (meets x y)
open meets renaming
  ( meet≤l to ∩≤l
  ; meet≤r to ∩≤r
  ; greatest to ∩-universal)
  public

abstract
  ∩-idem : ∀ {x} → x ∩ x ＝ x
  ∩-idem = ≤-antisym ∩≤l (∩-universal _ ≤-refl ≤-refl)

  ∩-comm : ∀ {x y} → x ∩ y ＝ y ∩ x
  ∩-comm =
    ≤-antisym
      (∩-universal _ ∩≤r ∩≤l)
      (∩-universal _ ∩≤r ∩≤l)

  ∩-assoc : ∀ {x y z} → x ∩ (y ∩ z) ＝ (x ∩ y) ∩ z
  ∩-assoc =
    ≤-antisym
      (∩-universal _
        (∩-universal _ ∩≤l (≤-trans ∩≤r ∩≤l))
        (≤-trans ∩≤r ∩≤r))
      (∩-universal _
        (≤-trans ∩≤l ∩≤l)
        (∩-universal _ (≤-trans ∩≤l ∩≤r) ∩≤r))

  ∩-is-semigroup : is-semigroup _∩_
  ∩-is-semigroup .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = ob-is-set
  ∩-is-semigroup .is-semigroup.assoc _ _ _ = ∩-assoc

  ∩≤∩
    : ∀ {x y x' y'}
    → x ≤ x'
    → y ≤ y'
    → (x ∩ y) ≤ (x' ∩ y')
  ∩≤∩ p q = ∩-universal _ (≤-trans ∩≤l p) (≤-trans ∩≤r q)

  ∩≤∩l : ∀ {x y x'} → x ≤ x' → (x ∩ y) ≤ (x' ∩ y)
  ∩≤∩l p = ∩≤∩ p ≤-refl

  ∩≤∩r : ∀ {x y y'} → y ≤ y' → (x ∩ y) ≤ (x ∩ y')
  ∩≤∩r p = ∩≤∩ ≤-refl p

  ∩→order : ∀ {x y} → x ∩ y ＝ x → x ≤ y
  ∩→order {x} {y} p =
    x       =⟨ p ⟨
    (x ∩ y) ≤⟨ ∩≤r ⟩
    y       ∎

  order→∩ : ∀ {x y} → x ≤ y → x ∩ y ＝ x
  order→∩ {x} {y} p = ≤-antisym ∩≤l (∩-universal _ ≤-refl p)

  ∩≃order : ∀ {x y} → (x ∩ y ＝ x) ≃ (x ≤ y)
  ∩≃order = prop-extₑ! ∩→order order→∩
