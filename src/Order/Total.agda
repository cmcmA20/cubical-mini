{-# OPTIONS --safe #-}
module Order.Total where

open import Cat.Prelude

open import Data.Empty
open import Data.Sum
open import Data.Dec

open import Order.Base
open import Order.Strict
open import Order.Diagram.Join
open import Order.Diagram.Meet

private variable o ℓ : Level

record is-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open Poset P public

  field
    compare : ∀ x y → x ≤ y ⊎ y ≤ x

module minmax {o ℓ} {P : Poset o ℓ} (to : is-total-order P) where
  open is-total-order to

  min : (x y : ⌞ P ⌟) → ⌞ P ⌟
  min x y = [ (λ _ → x) , (λ _ → y) ]ᵤ (compare x y)

  abstract
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

  max : (x y : ⌞ P ⌟) → ⌞ P ⌟
  max x y = [ (λ _ → y) , (λ _ → x) ]ᵤ (compare x y)

  abstract
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
is-decidable-poset P = ∀ {x y} → Dec (x ≤ y)
  where open Poset P

record is-decidable-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  field
    has-is-total : is-total-order P

  open is-total-order has-is-total public

  field
    ⦃ dec-≤    ⦄ : is-decidable-poset P
    ⦃ discrete ⦄ : is-discrete ⌞ P ⌟

  private
    was-discrete-anyways : is-discrete ⌞ P ⌟
    was-discrete-anyways {x} {y} with (dec-≤ {x} {y}) | (dec-≤ {x = y} {y = x})
    ... | yes x≤y | yes y≤x = yes (≤-antisym x≤y y≤x)
    ... | yes x≤y | no ¬y≤x = no λ x=y → ¬y≤x $ subst (_≤ x) x=y refl
    ... | no ¬x≤y | _       = no λ x=y → ¬x≤y $ subst (x ≤_) x=y refl

record is-weak-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open Poset P public

  field
    from-nleq : ∀ {x y} → ¬ (x ≤ y) → y ≤ x

module _ {o ℓ} {P : Poset o ℓ} ⦃ di : is-discrete ⌞ P ⌟ ⦄ ⦃ de : is-decidable-poset P ⦄ where
  open Poset P

  from-weak-total-order
    : is-weak-total-order P
    → is-decidable-total-order P
  from-weak-total-order wto .is-decidable-total-order.has-is-total .is-total-order.compare = cmp
    where
    cmp : (x y : Ob) → x ≤ y ⊎ y ≤ x
    cmp x y with (de {x} {y})
    ... | yes x≤y = inl x≤y
    ... | no ¬x≤y = inr $ wto .is-weak-total-order.from-nleq ¬x≤y
  from-weak-total-order wto .is-decidable-total-order.dec-≤ = de
  from-weak-total-order wto .is-decidable-total-order.discrete = di

record is-strict-total-order {o ℓ} (S : StrictPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open StrictPoset S public

  field
    weak-linear : ∀ x y z → x < z → x < y ⊎ y < z
    connex      : ∀ x y → ¬ (x < y) → ¬ (y < x) → x ＝ y

is-decidable-strictposet : ∀ {o ℓ} (S : StrictPoset o ℓ) → 𝒰 (o ⊔ ℓ)
is-decidable-strictposet S = ∀ {x y} → Dec (x < y)
  where open StrictPoset S

record is-decidable-strict-total-order {o ℓ} (S : StrictPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  field
    has-is-strict-total : is-strict-total-order S

  open is-strict-total-order has-is-strict-total public

  field
    ⦃ dec-<    ⦄ : is-decidable-strictposet S
    ⦃ discrete ⦄ : is-discrete ⌞ S ⌟
