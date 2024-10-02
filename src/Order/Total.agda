{-# OPTIONS --safe #-}
module Order.Total where

open import Cat.Prelude

open import Order.Base
open import Order.Strict
open import Order.Diagram.Join
open import Order.Diagram.Meet

open import Data.Bool.Base as Bool
open import Data.Dec as Dec
open import Data.Sum

private variable o ℓ : Level

record is-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open Poset P public

  field compare : ∀ x y → (x ≤ y) ⊎ (y ≤ x)

module minmax {o ℓ} {P : Poset o ℓ} (to : is-total-order P) where
  open is-total-order to

  min : (x y : Ob) → Ob
  min x y = [ (λ _ → x) , (λ _ → y) ]ᵤ (compare x y)

  opaque
    min-≤l : ∀ x y → min x y ≤ x
    min-≤l x y with compare x y
    ... | inl _ = ≤-refl
    ... | inr q = q

    min-≤r : ∀ x y → min x y ≤ y
    min-≤r x y with compare x y
    ... | inl p = p
    ... | inr _ = ≤-refl

    min-univ : ∀ x y z → z ≤ x → z ≤ y → z ≤ min x y
    min-univ x y z p q with compare x y
    ... | inl _ = p
    ... | inr _ = q

  min-is-meet : ∀ x y → is-meet P x y (min x y)
  min-is-meet x y .is-meet.meet≤l = min-≤l x y
  min-is-meet x y .is-meet.meet≤r = min-≤r x y
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


is-decidable-poset : ∀ {o ℓ} (P : Poset o ℓ) → 𝒰 (o ⊔ ℓ)
is-decidable-poset P = ∀ {x y} → Dec (x ≤ y) where open Poset P

instance
  Decidability-Poset : ∀ {o ℓ} → Decidability (Poset o ℓ)
  Decidability-Poset .Decidability.ℓ-decidability = _
  Decidability-Poset .Decidability.Decidable = is-decidable-poset


record is-decidable-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  field has-is-total : is-total-order P

  open is-total-order has-is-total public

  field
    ⦃ dec-≤        ⦄ : Decidable P
    ⦃ has-discrete ⦄ : is-discrete Ob

  infix 4.5 _≤?_ _≥?_ _≰?_ _≱?_
  _≤?_ _≥?_ _≰?_ _≱?_ : Ob → Ob → Bool
  x ≤? y = ⌊ dec-≤ {x} {y} ⌋
  _≥?_ = flip _≤?_
  x ≰? y = not (x ≤? y)
  x ≱? y = not (x ≥? y)

make-dec-total-order
  : {P : Poset o ℓ}
  → is-total-order P → Decidable P
  → is-decidable-total-order P
make-dec-total-order t d .is-decidable-total-order.has-is-total = t
make-dec-total-order t d .is-decidable-total-order.dec-≤ = d
make-dec-total-order {P} t d .is-decidable-total-order.has-discrete {x} {y}
  with d {x} {y} | d {y} {x}
... | yes x≤y | yes y≤x = yes (Poset.≤-antisym P x≤y y≤x)
... | yes x≤y | no ¬y≤x = no λ x=y → ¬y≤x $ subst (λ z → P .Poset._≤_ z x) x=y (P .Poset.≤-refl)
... | no ¬x≤y | _       = no λ x=y → ¬x≤y $ subst (λ z → P .Poset._≤_ x z) x=y (P .Poset.≤-refl)


record is-weak-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open Poset P public

  field from-≰ : ∀ {x y} → x ≰ y → y ≤ x

module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P

  dec-total-order→weak-total-order
    : is-decidable-total-order P → is-weak-total-order P
  dec-total-order→weak-total-order dto .is-weak-total-order.from-≰ {x} {y} =
    [ (λ x≤y x≰y → ⊥.rec (x≰y x≤y)) , (λ z _ → z) ]ᵤ
      (is-decidable-total-order.compare dto x y)

  weak-total-order→dec-total-order
    : ⦃ di : is-discrete Ob ⦄ ⦃ de : Decidable P ⦄
    → is-weak-total-order P → is-decidable-total-order P
  weak-total-order→dec-total-order ⦃ de ⦄ wto .is-decidable-total-order.has-is-total .is-total-order.compare x y =
    Dec.rec inl (inr ∘ₜ wto .is-weak-total-order.from-≰) (de {x} {y})


record is-strict-total-order {o ℓ} (S : StrictPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open StrictPoset S public

  field
    weak-linear : ∀ x y z → x < z → (x < y) ⊎ (y < z)
    connex      : ∀ x y → x ≮ y → y ≮ x → x ＝ y

is-decidable-strict-poset : ∀ {o ℓ} (S : StrictPoset o ℓ) → 𝒰 (o ⊔ ℓ)
is-decidable-strict-poset S = ∀ {x y} → Dec (x < y) where open StrictPoset S

instance
  Decidability-StrictPoset : ∀ {o ℓ} → Decidability (StrictPoset o ℓ)
  Decidability-StrictPoset .Decidability.ℓ-decidability = _
  Decidability-StrictPoset .Decidability.Decidable = is-decidable-strict-poset


record is-decidable-strict-total-order {o ℓ} (S : StrictPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  field has-is-strict-total : is-strict-total-order S

  open is-strict-total-order has-is-strict-total public

  field
    ⦃ dec-<        ⦄ : Decidable S
    ⦃ has-discrete ⦄ : is-discrete Ob

  infix 4.5 _<?_ _>?_ _≮?_ _≯?_
  _<?_ _>?_ _≮?_ _≯?_ : Ob → Ob → Bool
  x <? y = ⌊ dec-< {x} {y} ⌋
  _>?_ = flip _<?_
  x ≮? y = not (x <? y)
  x ≯? y = not (x >? y)

make-dec-strict-total-order
  : {S : StrictPoset o ℓ}
  → is-strict-total-order S → Decidable S
  → is-decidable-strict-total-order S
make-dec-strict-total-order sto d .is-decidable-strict-total-order.has-is-strict-total = sto
make-dec-strict-total-order sto d .is-decidable-strict-total-order.dec-< = d
make-dec-strict-total-order {S} sto d .is-decidable-strict-total-order.has-discrete {x} {y}
  with d {x} {y} | d {y} {x}
... | yes x<y | _  = no $ StrictPoset.<→≠ S x<y
... | no  x≮y | yes y<x = no λ x=y → StrictPoset.<→≠ S y<x (x=y ⁻¹)
... | no  x≮y | no  y≮x = yes (sto .is-strict-total-order.connex x y x≮y y≮x)
