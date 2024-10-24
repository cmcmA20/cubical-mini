{-# OPTIONS --safe #-}
module Order.Constructions.Minmax where

open import Cat.Prelude

open import Order.Base
open import Order.Diagram.Join
open import Order.Diagram.Join.Reasoning
open import Order.Diagram.Meet
open import Order.Diagram.Meet.Reasoning
open import Order.Total

open import Data.Bool.Base
open import Data.Dec
open import Data.Sum.Base

private variable o ℓ : Level

module minmax {o ℓ} {P : Poset o ℓ} (to : is-total-order P) where
  open is-total-order to

  min : (x y : Ob) → Ob
  min x y = [ (λ _ → x) , (λ _ → y) ]ᵤ (compare x y)

  opaque
    min≤l : ∀ x y → min x y ≤ x
    min≤l x y with compare x y
    ... | inl _ = ≤-refl
    ... | inr q = q

    min≤r : ∀ x y → min x y ≤ y
    min≤r x y with compare x y
    ... | inl p = p
    ... | inr _ = ≤-refl

    min-univ : ∀ x y z → z ≤ x → z ≤ y → z ≤ min x y
    min-univ x y z p q with compare x y
    ... | inl _ = p
    ... | inr _ = q

  min-is-meet : ∀ x y → is-meet P x y (min x y)
  min-is-meet x y .is-meet.meet≤l = min≤l x y
  min-is-meet x y .is-meet.meet≤r = min≤r x y
  min-is-meet x y .is-meet.greatest =  min-univ x y

  min-Meet : Has-meets P
  min-Meet {x} {y} .Meet.glb = min x y
  min-Meet {x} {y} .Meet.has-meet = min-is-meet x y

  min→≤⊎ : ∀ x y z → min x y ≤ z → (x ≤ z) ⊎ (y ≤ z)
  min→≤⊎ x y z min≤z with compare x y
  ... | inl _ = inl min≤z
  ... | inr _ = inr min≤z

  min≃≤⊎₁ : ∀ x y z → min x y ≤ z ≃ (x ≤ z) ⊎₁ (y ≤ z)
  min≃≤⊎₁ x y z = prop-extₑ! (∣_∣₁ ∘ₜ min→≤⊎ x y z) (elim! (≤⊎→∩ P min-Meet))

  max : (x y : Ob) → Ob
  max x y = [ (λ _ → y) , (λ _ → x) ]ᵤ (compare x y)

  opaque
    max-≤l : ∀ x y → x ≤ max x y
    max-≤l x y with compare x y
    ... | inl p = p
    ... | inr _ = ≤-refl

    max-≤r : ∀ x y → y ≤ max x y
    max-≤r x y with compare x y
    ... | inl _ = ≤-refl
    ... | inr q = q

    max-univ : ∀ x y z → x ≤ z → y ≤ z → max x y ≤ z
    max-univ x y z p q with compare x y
    ... | inl _ = q
    ... | inr _ = p

  max-is-join : ∀ x y → is-join P x y (max x y)
  max-is-join x y .is-join.l≤join = max-≤l x y
  max-is-join x y .is-join.r≤join = max-≤r x y
  max-is-join x y .is-join.least  = max-univ x y

  max-Join : Has-joins P
  max-Join {x} {y} .Join.lub = max x y
  max-Join {x} {y} .Join.has-join = max-is-join x y

  max→≤⊎ : ∀ x y z → z ≤ max x y → (z ≤ x) ⊎ (z ≤ y)
  max→≤⊎ x y z z≤max with compare x y
  ... | inl _ = inr z≤max
  ... | inr _ = inl z≤max

  max≃≤⊎₁ : ∀ x y z → z ≤ max x y ≃ (z ≤ x) ⊎₁ (z ≤ y)
  max≃≤⊎₁ x y z = prop-extₑ! (∣_∣₁ ∘ₜ max→≤⊎ x y z) (elim! (≤⊎→∪ P max-Join))

module minmaxprops {o ℓ o′ ℓ′} {P : Poset o ℓ} (toP : is-total-order P) {Q : Poset o′ ℓ′} (toQ : is-total-order Q) where
  private
    module Pt = is-total-order toP
    module Qt = is-total-order toQ
    module Pm = minmax toP
    module Qm = minmax toQ

  min-ap : ∀ (f : P ⇒ Q) (x y : ⌞ P ⌟)
         → Qm.min (f $ x) (f $ y) ＝ (f $ Pm.min x y)
  min-ap f x y with Pt.compare x y
  min-ap f x y | inl x≤y with Qt.compare (f $ x) (f $ y)
  min-ap f x y | inl x≤y | inl fx≤fy = refl
  min-ap f x y | inl x≤y | inr fy≤fx = Qt.≤-antisym fy≤fx (f .pres-≤ x≤y)
  min-ap f x y | inr y≤x with Qt.compare (f $ x) (f $ y)
  min-ap f x y | inr y≤x | inl fx≤fy = Qt.≤-antisym fx≤fy (f .pres-≤ y≤x)
  min-ap f x y | inr y≤x | inr fy≤fx = refl

  max-ap : ∀ (f : P ⇒ Q) (x y : ⌞ P ⌟)
         → Qm.max (f $ x) (f $ y) ＝ (f $ Pm.max x y)
  max-ap f x y with Pt.compare x y
  max-ap f x y | inl x≤y with Qt.compare (f $ x) (f $ y)
  max-ap f x y | inl x≤y | inl fx≤fy = refl
  max-ap f x y | inl x≤y | inr fy≤fx = Qt.≤-antisym (f .pres-≤ x≤y) fy≤fx
  max-ap f x y | inr y≤x with Qt.compare (f $ x) (f $ y)
  max-ap f x y | inr y≤x | inl fx≤fy = Qt.≤-antisym (f .pres-≤ y≤x) fx≤fy
  max-ap f x y | inr y≤x | inr fy≤fx = refl

module decminmax {o ℓ} {P : Poset o ℓ} (dto : is-decidable-total-order P) where
  open is-decidable-total-order dto

  min : (x y : Ob) → Ob
  min x y = if x ≤? y then x else y

  opaque
    min≤l : ∀ x y → min x y ≤ x
    min≤l x y with dec-≤ {x} {y}
    ... | yes x≤y = ≤-refl
    ... | no  x≰y with compare x y
    ... | inl x≤y = ⊥.rec (x≰y x≤y)
    ... | inr y≤x = y≤x

    min≤r : ∀ x y → min x y ≤ y
    min≤r x y with dec-≤ {x} {y}
    ... | yes x≤y = x≤y
    ... | no  x≰y = ≤-refl

    min-univ : ∀ x y z → z ≤ x → z ≤ y → z ≤ min x y
    min-univ x y z z≤x z≤y with dec-≤ {x} {y}
    ... | yes x≤y = z≤x
    ... | no  x≰y = z≤y

  min-is-meet : ∀ x y → is-meet P x y (min x y)
  min-is-meet x y .is-meet.meet≤l = min≤l x y
  min-is-meet x y .is-meet.meet≤r = min≤r x y
  min-is-meet x y .is-meet.greatest = min-univ x y

  min-Meet : Has-meets P
  min-Meet {x} {y} .Meet.glb = min x y
  min-Meet {x} {y} .Meet.has-meet = min-is-meet x y

  min→≤⊎ : ∀ x y z → min x y ≤ z → (x ≤ z) ⊎ (y ≤ z)
  min→≤⊎ x y z min≤z with dec-≤ {x} {y}
  ... | yes _ = inl min≤z
  ... | no  _ = inr min≤z

  min≃≤⊎₁ : ∀ x y z → min x y ≤ z ≃ (x ≤ z) ⊎₁ (y ≤ z)
  min≃≤⊎₁ x y z = prop-extₑ! (∣_∣₁ ∘ₜ min→≤⊎ x y z) (elim! (≤⊎→∩ P min-Meet))

  max : (x y : Ob) → Ob
  max x y = if x ≤? y then y else x

  opaque
    max-≤l : ∀ x y → x ≤ max x y
    max-≤l x y with dec-≤ {x} {y}
    ... | yes x≤y = x≤y
    ... | no  x≰y = ≤-refl

    max-≤r : ∀ x y → y ≤ max x y
    max-≤r x y with dec-≤ {x} {y}
    ... | yes x≤y = ≤-refl
    ... | no  x≰y with compare x y
    ... | inl x≤y = ⊥.rec (x≰y x≤y)
    ... | inr y≤x = y≤x

    max-univ : ∀ x y z → x ≤ z → y ≤ z → max x y ≤ z
    max-univ x y z x≤z y≤z with dec-≤ {x} {y}
    ... | yes x≤y = y≤z
    ... | no  x≰y = x≤z

  max-is-join : ∀ x y → is-join P x y (max x y)
  max-is-join x y .is-join.l≤join = max-≤l x y
  max-is-join x y .is-join.r≤join = max-≤r x y
  max-is-join x y .is-join.least  = max-univ x y

  max-Join : Has-joins P
  max-Join {x} {y} .Join.lub = max x y
  max-Join {x} {y} .Join.has-join = max-is-join x y

  max→≤⊎ : ∀ x y z → z ≤ max x y → (z ≤ x) ⊎ (z ≤ y)
  max→≤⊎ x y z z≤max with dec-≤ {x} {y}
  ... | yes _ = inr z≤max
  ... | no  _ = inl z≤max

  max≃≤⊎₁ : ∀ x y z → z ≤ max x y ≃ (z ≤ x) ⊎₁ (z ≤ y)
  max≃≤⊎₁ x y z = prop-extₑ! (∣_∣₁ ∘ₜ max→≤⊎ x y z) (elim! (≤⊎→∪ P max-Join))

module decminmaxprops {o ℓ o′ ℓ′} {P : Poset o ℓ} (dtoP : is-decidable-total-order P) {Q : Poset o′ ℓ′} (dtoQ : is-decidable-total-order Q) where
  private
    module Pt = is-decidable-total-order dtoP
    module Qt = is-decidable-total-order dtoQ
    module Pm = decminmax dtoP
    module Qm = decminmax dtoQ
    instance _ = Qt.dec-≤

  min-ap : ∀ (f : P ⇒ Q) (x y : ⌞ P ⌟)
         → Qm.min (f # x) (f # y) ＝ f # Pm.min x y
  min-ap f x y with Pt.dec-≤ {x} {y}
  min-ap f x y | yes x≤y =
    given-yes (f # x≤y) return (λ q → (if ⌊ q ⌋ then _ else _) ＝ _) then refl
  min-ap f x y | no x≰y with Qt.dec-≤ {f # x} {f # y}
  min-ap f x y | no x≰y | yes fx≤fy = Qt.≤-antisym fx≤fy (f # (Pt.≰→≥≠ x≰y .fst))
  min-ap f x y | no x≰y | no  fy≤fx = refl

  max-ap : ∀ (f : P ⇒ Q) (x y : ⌞ P ⌟)
         → Qm.max (f # x) (f # y) ＝ f # Pm.max x y
  max-ap f x y with Pt.dec-≤ {x} {y}
  max-ap f x y | yes x≤y =
    given-yes (f # x≤y) return (λ q → (if ⌊ q ⌋ then _ else _) ＝ _) then refl
  max-ap f x y | no x≰y with Qt.dec-≤ {f # x} {f # y}
  max-ap f x y | no x≰y | yes fx≤fy = Qt.≤-antisym (f # (Pt.≰→≥≠ x≰y .fst)) fx≤fy
  max-ap f x y | no x≰y | no  fy≤fx = refl
