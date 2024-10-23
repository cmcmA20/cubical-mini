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

-- aka toset
record is-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  no-eta-equality
  open Poset P public

  field compare : ∀ x y → (x ≤ y) ⊎ (x ≥ y)

  ≰→≥≠ : ∀ {x y} → x ≰ y → (x ≥ y) × (x ≠ y)
  ≰→≥≠ {x} {y} x≰y with compare x y
  ... | inl x≤y = ⊥.rec (x≰y x≤y)
  ... | inr y≤x = y≤x , ⊥.contra =→≤ x≰y

  converse-complement : StrictPoset o ℓ
  converse-complement .StrictPoset.Ob = Ob
  converse-complement .StrictPoset._<_ x y = y ≰ x
  converse-complement .StrictPoset.<-thin = hlevel 1
  converse-complement .StrictPoset.<-irrefl nx = nx refl
  converse-complement .StrictPoset.<-trans {x} {y} nyx nzy zx =
    [ ≤-trans zx ∙ nzy , nyx ]ᵤ (compare x y)

is-decidable-poset : ∀ {o ℓ} (P : Poset o ℓ) → 𝒰 (o ⊔ ℓ)
is-decidable-poset P = ∀ {x y} → Dec (x ≤ y) where open Poset P

instance
  Decidability-Poset : ∀ {o ℓ} → Decidability (Poset o ℓ)
  Decidability-Poset .Decidability.ℓ-decidability = _
  Decidability-Poset .Decidability.Decidable = is-decidable-poset


record is-decidable-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  no-eta-equality
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

dec+total→dec-total-order
  : {P : Poset o ℓ}
  → Decidable P → is-total-order P
  → is-decidable-total-order P
dec+total→dec-total-order d t .is-decidable-total-order.has-is-total = t
dec+total→dec-total-order d t .is-decidable-total-order.dec-≤ = d
dec+total→dec-total-order {P} d t .is-decidable-total-order.has-discrete {x} {y}
  with d {x} {y} | d {y} {x}
... | yes x≤y | yes y≤x = yes (Poset.≤-antisym P x≤y y≤x)
... | yes x≤y | no ¬y≤x = no λ x=y → ¬y≤x $ subst (λ z → P .Poset._≤_ z x) x=y (P .Poset.≤-refl)
... | no ¬x≤y | _       = no λ x=y → ¬x≤y $ subst (λ z → P .Poset._≤_ x z) x=y (P .Poset.≤-refl)


record is-weak-total-order {o ℓ} (P : Poset o ℓ) : 𝒰 (o ⊔ ℓ) where
  no-eta-equality
  open Poset P public

  field from-≰ : ∀ {x y} → x ≰ y → x ≥ y

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


-- aka loset
record is-strict-total-order {o ℓ} (S : StrictPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open StrictPoset S public

  field
    <-weak-linear : ∀ {x y z} → x < z → (x < y) ⊎ (y < z)
    <-connex      : ∀ {x y} → x ≮ y → y ≮ x → x ＝ y

  converse-complement : Poset o ℓ
  converse-complement .Poset.Ob = Ob
  converse-complement .Poset._≤_ x y = y ≯ x
  converse-complement .Poset.≤-thin = hlevel 1
  converse-complement .Poset.≤-refl = <-irrefl
  converse-complement .Poset.≤-trans x≮y y≮z x<z = [ x≮y , y≮z ]ᵤ (<-weak-linear x<z)
  converse-complement .Poset.≤-antisym x≮y y≮x = <-connex x≮y y≮x

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

dec+strict-total→dec-strict-total-order
  : {S : StrictPoset o ℓ}
  → Decidable S → is-strict-total-order S
  → is-decidable-strict-total-order S
dec+strict-total→dec-strict-total-order d sto .is-decidable-strict-total-order.has-is-strict-total = sto
dec+strict-total→dec-strict-total-order d sto .is-decidable-strict-total-order.dec-< = d
dec+strict-total→dec-strict-total-order {S} d sto .is-decidable-strict-total-order.has-discrete {x} {y}
  with d {x} {y} | d {y} {x}
... | yes x<y | _  = no $ StrictPoset.<→≠ S x<y
... | no  x≮y | yes y<x = no λ x=y → StrictPoset.<→≠ S y<x (x=y ⁻¹)
... | no  x≮y | no  y≮x = yes (sto .is-strict-total-order.<-connex x≮y y≮x)

module _ {S : StrictPoset o ℓ} where
  open StrictPoset S

  discrete+dec+connnex→dec-strict-total-order
    : is-discrete Ob → Decidable S
    → (∀{x y} → x ≮ y → y ≮ x → x ＝ y)
    → is-decidable-strict-total-order S
  discrete+dec+connnex→dec-strict-total-order di d co
    .is-decidable-strict-total-order.has-is-strict-total
    .is-strict-total-order.<-weak-linear {x} {y} {z} x<z with d {x} {y}
  ... | yes x<y = inl x<y
  ... | no  x≮y with d {y} {z}
  ... | yes y<z = inr y<z
  ... | no  y≮z =
    let u = co (λ y<x → y≮z (y<x ∙ x<z)) x≮y
        v = co (λ z<y → x≮y (x<z ∙ z<y)) y≮z
     in ⊥.rec (<-irrefl (subst (_ <_) (v ∙ u) x<z))
  discrete+dec+connnex→dec-strict-total-order di d co
    .is-decidable-strict-total-order.has-is-strict-total
    .is-strict-total-order.<-connex = co
  discrete+dec+connnex→dec-strict-total-order di d co
    .is-decidable-strict-total-order.dec-< = d
  discrete+dec+connnex→dec-strict-total-order di d co
    .is-decidable-strict-total-order.has-discrete = di
