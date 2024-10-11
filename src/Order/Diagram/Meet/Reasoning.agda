{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Top
open import Order.Diagram.Meet
open import Data.Sum.Base

module Order.Diagram.Meet.Reasoning
  {o ℓ} (P : Poset o ℓ) (hm : Has-meets P)
  where

open import Algebra.Semigroup
open import Algebra.Monoid.Commutative
open import Cat.Prelude

open Poset P
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

private variable x y x′ y′ z : Ob

opaque
  ∩-idem : x ∩ x ＝ x
  ∩-idem = ≤-antisym ∩≤l (∩-universal _ refl refl)

  ∩-comm : x ∩ y ＝ y ∩ x
  ∩-comm =
    ≤-antisym
      (∩-universal _ ∩≤r ∩≤l)
      (∩-universal _ ∩≤r ∩≤l)

  ∩-assoc : x ∩ y ∩ z ＝ (x ∩ y) ∩ z
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
    : x ≤ x′
    → y ≤ y′
    → (x ∩ y) ≤ (x′ ∩ y′)
  ∩≤∩ p q = ∩-universal _ (∩≤l ∙ p) (∩≤r ∙ q)

  ∩≤∩-l : x ≤ x′ → x ∩ y ≤ x′ ∩ y
  ∩≤∩-l p = ∩≤∩ p refl

  ∩≤∩-r : y ≤ y′ → (x ∩ y) ≤ (x ∩ y′)
  ∩≤∩-r p = ∩≤∩ refl p

  ∩→order : x ∩ y ＝ x → x ≤ y
  ∩→order {x} {y} p =
    x      =⟨ p ⟨
    x ∩ y  ≤⟨ ∩≤r ⟩
    y      ∎

  order→∩ : x ≤ y → x ∩ y ＝ x
  order→∩ {x} {y} p = ≤-antisym ∩≤l (∩-universal _ refl p)

  ∩≃order : (x ∩ y ＝ x) ≃ (x ≤ y)
  ∩≃order = prop-extₑ! ∩→order order→∩

  ∩≃≤× : z ≤ x ∩ y ≃ (z ≤ x) × (z ≤ y)
  ∩≃≤× = prop-extₑ! (λ z≤∩ → z≤∩ ∙ ∩≤l , z≤∩ ∙ ∩≤r) λ where (z≤x , z≤y) → ∩-universal _ z≤x z≤y

  ≤⊎→∩ : (x ≤ z) ⊎ (y ≤ z) → x ∩ y ≤ z
  ≤⊎→∩ = [ ∩≤l ∙_ , ∩≤r ∙_ ]ᵤ

module _ ⦃ b : Bottom P ⦄ where opaque
  open Bottom b

  ∩-absorb-l : ⊥ ∩ x ＝ ⊥
  ∩-absorb-l = ≤-antisym ∩≤l ¡

  ∩-absorb-r : x ∩ ⊥ ＝ ⊥
  ∩-absorb-r = ≤-antisym ∩≤r ¡

module _ ⦃ t : Top P ⦄ where opaque
  open Top t

  ∩-id-l : ⊤ ∩ x ＝ x
  ∩-id-l = ∩-comm ∙ order→∩ !

  ∩-id-r : x ∩ ⊤ ＝ x
  ∩-id-r = order→∩ !

  ∩-is-monoid : is-monoid {A = Ob} _∩_
  ∩-is-monoid .is-monoid.has-semigroup = ∩-is-semigroup
  ∩-is-monoid .is-monoid.id = ⊤
  ∩-is-monoid .is-monoid.id-l _ = ∩-id-l
  ∩-is-monoid .is-monoid.id-r _ = ∩-id-r

  ∩-is-comm-monoid : is-comm-monoid {A = Ob} _∩_
  ∩-is-comm-monoid .is-comm-monoid.has-monoid = ∩-is-monoid
  ∩-is-comm-monoid .is-comm-monoid.comm _ _ = ∩-comm
