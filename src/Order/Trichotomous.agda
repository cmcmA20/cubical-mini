{-# OPTIONS --safe #-}
module Order.Trichotomous where

open import Cat.Prelude

open import Data.Empty
open import Data.Sum
open import Data.Dec
open import Data.Tri renaming (elim to elimᵗ ; rec to recᵗ)

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

module _ {o ℓ} {S : StrictPoset o ℓ} ⦃ t : is-trichotomous S ⦄ where
  open StrictPoset S

  Tri→strict-total : is-strict-total-order S
  Tri→strict-total .is-strict-total-order.weak-linear x y z x<z =
    elimᵗ (λ x<y x≠y y≮x → inl x<y)
          (λ x≮y x=y y≮x → inr (subst (_< z) x=y x<z))
          (λ x≮y x≠y y<x → inr (<-trans y<x x<z))
          (t .is-trichotomous.trisect x y)
  Tri→strict-total .is-strict-total-order.connex x y x≮y y≮x =
    elimᵗ (λ x<y _ _ → absurd (x≮y x<y))
          (λ _ x=y _ → x=y)
          (λ _ _ y<x → absurd (y≮x y<x))
          (t .is-trichotomous.trisect x y)

  Tri→dec-strict-poset : is-decidable-strictposet S
  Tri→dec-strict-poset {x} {y} = ⌊ t .is-trichotomous.trisect x y ⌋<¿

  Tri→discrete : is-discrete Ob
  Tri→discrete {x} {y} = ⌊ t .is-trichotomous.trisect x y ⌋≟

  Tri→DSTO : is-decidable-strict-total-order S
  Tri→DSTO .is-decidable-strict-total-order.has-is-strict-total = Tri→strict-total
  Tri→DSTO .is-decidable-strict-total-order.dec-<               = Tri→dec-strict-poset
  Tri→DSTO .is-decidable-strict-total-order.discrete            = Tri→discrete

  caseᵗ_>=<_of_ : {ℓᵃ : Level} {A : 𝒰 ℓᵃ}
                → (x y : Ob)
                → (Tri _<_ x y → A) → A
  caseᵗ_>=<_of_ x y f = f (t .is-trichotomous.trisect x y)
  {-# INLINE caseᵗ_>=<_of_ #-}

  caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ : {ℓᵃ : Level} {A : 𝒰 ℓᵃ}
                         → (x y : Ob)
                         → A → A → A → A
  caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ x y l e g = recᵗ l e g (t .is-trichotomous.trisect x y)
  {-# INLINE caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ #-}

  caseᵗ_>=<_return_of_ : {ℓᵃ : Level}
                       → (x y : Ob) (A : Tri _<_ x y → 𝒰 ℓᵃ)
                       → (∀ t → A t) → A (t .is-trichotomous.trisect x y)
  caseᵗ_>=<_return_of_ x y A f = f (t .is-trichotomous.trisect x y)
  {-# INLINE caseᵗ_>=<_of_ #-}

  given-lt_return_then_ : {ℓᵃ : Level} {x y : Ob}
                        → (x<y : x < y)
                        → (A : Tri _<_ x y → 𝒰 ℓᵃ)
                        → A (lt x<y (<→≠ x<y) (<-asym x<y))
                        → A (t .is-trichotomous.trisect x y)
  given-lt_return_then_ {x} {y} x<y A alt =
    elimᵗ {C = A}
      (λ x<y′ x≠y y≮x →
         subst (λ q → A (lt q x≠y y≮x)) prop! $
         subst (λ q → A (lt x<y q y≮x)) prop! $
         subst (λ q → A (lt x<y (<→≠ x<y) q)) prop! alt)
      (λ _ x=y _ → absurd (<→≠ x<y x=y))
      (λ x≮y _ _ → absurd (x≮y x<y))
      (t .is-trichotomous.trisect x y)

  given-eq_return_then_ : {ℓᵃ : Level} {x y : Ob}
                        → (x=y : x ＝ y)
                        → (A : Tri _<_ x y → 𝒰 ℓᵃ)
                        → A (eq (=→≮ x=y) x=y (=→≮ $ x=y ⁻¹))
                        → A (t .is-trichotomous.trisect x y)
  given-eq_return_then_ {x} {y} x=y A aeq =
    elimᵗ {C = A}
      (λ _ x≠y _ → absurd (x≠y x=y))
      (λ x≮y x=y′ y≮x →
       subst (λ q → A (eq q x=y′ y≮x)) prop! $
       subst (λ q → A (eq (=→≮ x=y) q y≮x)) (path-is-of-hlevel 1 (is-discrete→is-set Tri→discrete) x y x=y x=y′) $
       subst (λ q → A (eq (=→≮ x=y) x=y q)) prop! aeq)
      (λ _ x≠y _ → absurd (x≠y x=y))
      (t .is-trichotomous.trisect x y)

  given-gt_return_then_ : {ℓᵃ : Level} {x y : Ob}
                        → (y<x : y < x)
                        → (A : Tri _<_ x y → 𝒰 ℓᵃ)
                        → A (gt (<-asym y<x) (<→≠ y<x ∘ₜ _⁻¹) y<x)
                        → A (t .is-trichotomous.trisect x y)
  given-gt_return_then_ {x} {y} y<x A agt =
    elimᵗ {C = A}
      (λ _ _ y≮x → absurd (y≮x y<x))
      (λ _ x=y _ → absurd (<→≠ y<x (x=y ⁻¹)))
      (λ x≮y x≠y y<x′ →
        subst (λ q → A (gt q x≠y y<x′)) prop! $
        subst (λ q → A (gt (<-asym y<x) q y<x′)) prop! $
        subst (λ q → A (gt (<-asym y<x) (<→≠ y<x ∘ₜ _⁻¹) q)) prop! agt)
      (t .is-trichotomous.trisect x y)

