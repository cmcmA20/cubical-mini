{-# OPTIONS --safe #-}
module Order.Constructions.Minmax where

open import Cat.Prelude

open import Order.Base
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Total

open import Data.Bool.Base
open import Data.Dec.Base
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
  min-is-meet x y .is-meet.greatest =  min-univ x y

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
