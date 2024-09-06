{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Meet

module Order.Diagram.Meet.Reasoning
  {o ℓ} (P : Poset o ℓ) (hm : Has-meets P)
  where

open import Algebra.Semigroup
open import Cat.Prelude

open import Order.Reasoning P
open Meet

instance
  Intersection-Poset : Intersection Ob Ob Ob
  Intersection-Poset ._∩_ x y = hm {x} {y} .glb

meets : ∀ x y → Meet P x y
meets x y .glb      = x ∩ y
meets x y .has-meet = hm .has-meet

module meets {x} {y} = Meet (meets x y)
open meets renaming
  ( meet≤l   to ∩≤l
  ; meet≤r   to ∩≤r
  ; greatest to ∩-universal)
  public

opaque
  ∩-idem : {x : Ob} → x ∩ x ＝ x
  ∩-idem = ≤-antisym ∩≤l (∩-universal _ refl refl)

  ∩-comm : {x y : Ob} → x ∩ y ＝ y ∩ x
  ∩-comm =
    ≤-antisym
      (∩-universal _ ∩≤r ∩≤l)
      (∩-universal _ ∩≤r ∩≤l)

  ∩-assoc : {x y z : Ob} → x ∩ y ∩ z ＝ (x ∩ y) ∩ z
  ∩-assoc =
    ≤-antisym
      (∩-universal _
        (∩-universal _ ∩≤l (∩≤r ∙ ∩≤l))
        (∩≤r ∙ ∩≤r))
      (∩-universal _
        (∩≤l ∙ ∩≤l)
        (∩-universal _ (∩≤l ∙ ∩≤r) ∩≤r))

  ∩-is-semigroup : is-semigroup {A = Ob} _∩_
  ∩-is-semigroup .is-semigroup.has-magma .is-n-magma.has-is-of-hlevel = ob-is-set
  ∩-is-semigroup .is-semigroup.assoc _ _ _ = ∩-assoc

  ∩≤∩
    : {x y x′ y′ : Ob}
    → x ≤ x′
    → y ≤ y′
    → (x ∩ y) ≤ (x′ ∩ y′)
  ∩≤∩ p q = ∩-universal _ (∩≤l ∙ p) (∩≤r ∙ q)

  ∩≤∩-l : {x y x′ : Ob} → x ≤ x′ → x ∩ y ≤ x′ ∩ y
  ∩≤∩-l p = ∩≤∩ p refl

  ∩≤∩-r : {x y y′ : Ob} → y ≤ y′ → (x ∩ y) ≤ (x ∩ y′)
  ∩≤∩-r p = ∩≤∩ refl p

  ∩→order : ∀ {x y} → x ∩ y ＝ x → x ≤ y
  ∩→order {x} {y} p =
    x      =⟨ p ⟨
    x ∩ y  ≤⟨ ∩≤r ⟩
    y      ∎

  order→∩ : ∀ {x y} → x ≤ y → x ∩ y ＝ x
  order→∩ {x} {y} p = ≤-antisym ∩≤l (∩-universal _ refl p)

  ∩≃order : ∀ {x y} → (x ∩ y ＝ x) ≃ (x ≤ y)
  ∩≃order = prop-extₑ! ∩→order order→∩
