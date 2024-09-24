{-# OPTIONS --safe #-}
module Order.Trichotomous where

open import Cat.Prelude

open import Data.Empty
open import Data.Sum
open import Data.Dec
open import Data.Tri

open import Order.Strict
open import Order.Total

record is-trichotomous {o ℓ} (S : StrictPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open StrictPoset S public

  field
    trisect : ∀ x y → Tri _<_ x y

module _ {o ℓ} {S : StrictPoset o ℓ} ⦃ d : is-decidable-strict-total-order S ⦄ where
  open StrictPoset S

  DSTO→Tri : is-trichotomous S
  DSTO→Tri .is-trichotomous.trisect x y with d .is-decidable-strict-total-order.discrete {x} {y}
  ... | yes x=y = eq (λ x<y → <-irrefl (subst (x <_) (x=y ⁻¹) x<y))
                     x=y
                     λ y<x → <-irrefl (subst (y <_) x=y y<x)
  ... | no x≠y with d .is-decidable-strict-total-order.dec-< {x} {y}
  ...          | yes x<y = lt x<y x≠y (<-asym x<y)
  ...          | no x≮y with d .is-decidable-strict-total-order.dec-< {x = y} {y = x}
  ...                   | yes y<x = gt x≮y x≠y y<x
  ...                   | no y≮x = absurd (x≠y (d .is-decidable-strict-total-order.connex x y x≮y y≮x))

             
module _ {o ℓ} {S : StrictPoset o ℓ} where
  open StrictPoset S

  Tri→DSTO : is-trichotomous S 
           → is-decidable-strict-total-order S
  Tri→DSTO t .is-decidable-strict-total-order.has-is-strict-total .is-strict-total-order.weak-linear x y z x<z =
    Tri-elim (λ x<y x≠y y≮x → inl x<y)
             (λ x≮y x=y y≮x → inr (subst (_< z) x=y x<z))
             (λ x≮y x≠y y<x → inr (<-trans y<x x<z))
             (t .is-trichotomous.trisect x y)
  Tri→DSTO t .is-decidable-strict-total-order.has-is-strict-total .is-strict-total-order.connex x y x≮y y≮x =
    Tri-elim (λ x<y _ _ → absurd (x≮y x<y))
             (λ _ x=y _ → x=y)
             (λ _ _ y<x → absurd (y≮x y<x))
             (t .is-trichotomous.trisect x y)
  Tri→DSTO t .is-decidable-strict-total-order.dec-< {x} {y} =
    Tri-elim (λ x<y _ _ → yes x<y)
             (λ x≮y _ _ → no x≮y)
             (λ x≮y _ _ → no x≮y)
             (t .is-trichotomous.trisect x y)
  Tri→DSTO t .is-decidable-strict-total-order.discrete {x} {y} =
    Tri-elim (λ _ x≠y _ → no x≠y)
             (λ _ x=y _ → yes x=y)
             (λ _ x≠y _ → no x≠y)
             (t .is-trichotomous.trisect x y)


