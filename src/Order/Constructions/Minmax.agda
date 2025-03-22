{-# OPTIONS --safe #-}
module Order.Constructions.Minmax where

open import Cat.Prelude

open import Order.Base
open import Order.Diagram.Join
import Order.Diagram.Join.Reasoning as JR
open import Order.Diagram.Meet
import Order.Diagram.Meet.Reasoning as MR
open import Order.Lattice
open import Order.Total

open import Data.Bool.Base
open import Data.Dec
open import Data.Sum.Base

private variable
  o ℓ : Level
  n : HLevel

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

  min-meets : Has-meets P
  min-meets {x} {y} .Meet.glb = min x y
  min-meets {x} {y} .Meet.has-meet = min-is-meet x y

  instance
    H-Level-meets : H-Level n (Has-meets P)
    H-Level-meets = hlevel-basic-instance 0 $
      inhabited-prop-is-contr (λ {x} {y} → min-meets)
      (∀-is-of-hlevel 1 λ _ → hlevel 1)
    {-# OVERLAPS H-Level-meets #-}

  open MR P min-meets

  min→≤⊎ : ∀ {x y z} → x ∩ y ≤ z → (x ≤ z) ⊎ (y ≤ z)
  min→≤⊎ {x} {y} min≤z with compare x y
  ... | inl _ = inl min≤z
  ... | inr _ = inr min≤z

  min≃≤⊎₁ : ∀ {x y z} → x ∩ y ≤ z ≃ (x ≤ z) ⊎₁ (y ≤ z)
  min≃≤⊎₁ = prop-extₑ! (∣_∣₁ ∘ₜ min→≤⊎) (elim! ≤⊎→∩)


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

  max-joins : Has-joins P
  max-joins {x} {y} .Join.lub = max x y
  max-joins {x} {y} .Join.has-join = max-is-join x y

  instance
    H-Level-joins : H-Level n (Has-joins P)
    H-Level-joins = hlevel-basic-instance 0 $
      inhabited-prop-is-contr (λ {x} {y} → max-joins)
      (∀-is-of-hlevel 1 λ _ → hlevel 1)
    {-# OVERLAPS H-Level-joins #-}

  open JR P max-joins

  max→≤⊎ : ∀ x y z → z ≤ x ∪ y → (z ≤ x) ⊎ (z ≤ y)
  max→≤⊎ x y z z≤max with compare x y
  ... | inl _ = inr z≤max
  ... | inr _ = inl z≤max

  max≃≤⊎₁ : ∀ x y z → z ≤ x ∪ y ≃ (z ≤ x) ⊎₁ (z ≤ y)
  max≃≤⊎₁ x y z = prop-extₑ! (∣_∣₁ ∘ₜ max→≤⊎ x y z) (elim! ≤⊎→∪)



module minmaxprops {o o′ ℓ ℓ′} {P : Poset o ℓ} {Q : Poset o′ ℓ′}
  (P-to : is-total-order P) (Q-to : is-total-order Q) where
  private
    module Pt = is-total-order P-to
    module Qt = is-total-order Q-to
    module Pm = minmax P-to
    module Qm = minmax Q-to
    module Pmr = MR P Pm.min-meets
    module Pjr = JR P Pm.max-joins
    module Qmr = MR Q Qm.min-meets
    module Qjr = JR Q Qm.max-joins

  opaque
    min-ap : (f : P ⇒ Q) (x y : ⌞ P ⌟)
           → f # (x ∩ y) ＝ (f # x) ∩ (f # y)
    min-ap f x y with Pt.compare x y
    min-ap f x y | inl x≤y with Qt.compare (f .hom x) (f .hom y)
    min-ap f x y | inl x≤y | inl fx≤fy = refl
    min-ap f x y | inl x≤y | inr fy≤fx = Qt.≤-antisym (f # x≤y) fy≤fx
    min-ap f x y | inr y≤x with Qt.compare (f .hom x) (f .hom y)
    min-ap f x y | inr y≤x | inl fx≤fy = Qt.≤-antisym (f # y≤x) fx≤fy
    min-ap f x y | inr y≤x | inr fy≤fx = refl

    max-ap : (f : P ⇒ Q) (x y : ⌞ P ⌟)
           → f # (x ∪ y) ＝ (f # x) ∪ (f # y)
    max-ap f x y with Pt.compare x y
    max-ap f x y | inl x≤y with Qt.compare (f .hom x) (f .hom y)
    max-ap f x y | inl x≤y | inl fx≤fy = refl
    max-ap f x y | inl x≤y | inr fy≤fx = Qt.≤-antisym fy≤fx (f # x≤y)
    max-ap f x y | inr y≤x with Qt.compare (f .hom x) (f .hom y)
    max-ap f x y | inr y≤x | inl fx≤fy = Qt.≤-antisym fx≤fy (f # y≤x)
    max-ap f x y | inr y≤x | inr fy≤fx = refl



module decminmax {o ℓ} {P : Poset o ℓ} (dto : is-decidable-total-order P) where
  open is-decidable-total-order dto

  private
    module tot = is-total-order has-is-total
    module tm = minmax has-is-total

  min : (x y : Ob) → Ob
  min x y = if x ≤? y then x else y

  total-min=dec-total-min : ∀ {x y} → tm.min x y ＝ min x y
  total-min=dec-total-min {x} {y} with tot.compare x y | dec-≤ {x} {y}
  ... | inl p | yes q = refl
  ... | inl p | no ¬q = ⊥.rec (¬q p)
  ... | inr p | yes q = ≤-antisym p q
  ... | inr p | no ¬q = refl

  min-meets : Has-meets P
  min-meets {x} {y} .Meet.glb = min x y
  min-meets {x} {y} .Meet.has-meet = =→is-meet total-min=dec-total-min (tm.min-is-meet x y)

  instance
    H-Level-meets : H-Level n (Has-meets P)
    H-Level-meets = hlevel-basic-instance 0 $
      inhabited-prop-is-contr (λ {x} {y} → min-meets)
      (∀-is-of-hlevel 1 λ _ → hlevel 1)
    {-# OVERLAPPING H-Level-meets #-}

  min→≤⊎ : ∀ {x y z} → min x y ≤ z → (x ≤ z) ⊎ (y ≤ z)
  min→≤⊎ {x} {y} min≤z with dec-≤ {x} {y}
  ... | yes _ = inl min≤z
  ... | no  _ = inr min≤z

  open MR P min-meets

  min≃≤⊎₁ : ∀ {x y z} → min x y ≤ z ≃ (x ≤ z) ⊎₁ (y ≤ z)
  min≃≤⊎₁ = prop-extₑ! (∣_∣₁ ∘ₜ min→≤⊎) (elim! ≤⊎→∩)


  max : (x y : Ob) → Ob
  max x y = if x ≤? y then y else x

  total-max=dec-total-max : ∀ {x y} → tm.max x y ＝ max x y
  total-max=dec-total-max {x} {y} with tot.compare x y | dec-≤ {x} {y}
  ... | inl p | yes q = refl
  ... | inl p | no ¬q = ⊥.rec (¬q p)
  ... | inr p | yes q = ≤-antisym q p
  ... | inr p | no ¬q = refl

  max-joins : Has-joins P
  max-joins {x} {y} .Join.lub = max x y
  max-joins {x} {y} .Join.has-join = =→is-join total-max=dec-total-max (tm.max-is-join x y)

  instance
    H-Level-joins : H-Level n (Has-joins P)
    H-Level-joins = hlevel-basic-instance 0 $
      inhabited-prop-is-contr (λ {x} {y} → max-joins)
      (∀-is-of-hlevel 1 λ _ → hlevel 1)
    {-# OVERLAPPING H-Level-joins #-}

  open JR P max-joins

  max→≤⊎ : ∀ {x y z} → z ≤ max x y → (z ≤ x) ⊎ (z ≤ y)
  max→≤⊎ {x} {y} z≤max with dec-≤ {x} {y}
  ... | yes _ = inr z≤max
  ... | no  _ = inl z≤max

  max≃≤⊎₁ : ∀ {x y z} → z ≤ max x y ≃ (z ≤ x) ⊎₁ (z ≤ y)
  max≃≤⊎₁ = prop-extₑ! (∣_∣₁ ∘ₜ max→≤⊎) (elim! ≤⊎→∪)


module decminmaxprops {o o′ ℓ ℓ′} {P : Poset o ℓ} {Q : Poset o′ ℓ′}
  (P-dto : is-decidable-total-order P) (Q-dto : is-decidable-total-order Q) where
  private
    module Pt = is-decidable-total-order P-dto
    module Qt = is-decidable-total-order Q-dto
    module Pm = decminmax P-dto
    module Qm = decminmax Q-dto
    module Pmr = MR P Pm.min-meets
    module Pjr = JR P Pm.max-joins
    module Qmr = MR Q Qm.min-meets
    module Qjr = JR Q Qm.max-joins
    module dmp = minmaxprops Pt.has-is-total Qt.has-is-total

  opaque
    min-ap : (f : P ⇒ Q) (x y : ⌞ P ⌟) → f # (x ∩ y) ＝ (f # x) ∩ (f # y)
    min-ap f x y = ap$ f (Pm.total-min=dec-total-min ⁻¹) ∙ dmp.min-ap f x y ∙ Qm.total-min=dec-total-min

    max-ap : (f : P ⇒ Q) (x y : ⌞ P ⌟) → f # (x ∪ y) ＝ (f # x) ∪ (f # y)
    max-ap f x y = ap$ f (Pm.total-max=dec-total-max ⁻¹) ∙ dmp.max-ap f x y ∙ Qm.total-max=dec-total-max
