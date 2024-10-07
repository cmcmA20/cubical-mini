{-# OPTIONS --safe #-}
module Order.Trichotomous where

open import Cat.Prelude

open import Order.Strict
open import Order.Total

open import Data.Dec
open import Data.Dec.Tri as Tri
open import Data.Sum

module _ {o ℓ} (S : StrictPoset o ℓ) where
  open StrictPoset S

  private variable x y : Ob

record is-trichotomous {o ℓ} (S : StrictPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open StrictPoset S public

  field trisect : ∀ x y → Tri _<_ x y

  instance
    Refl-Tri< : Refl (Tri _<_)
    Refl-Tri< .refl = EQ refl

    Sym-Tri< : Sym (Tri _<_)
    Sym-Tri< ._ᵒᵖ = Tri.elim GT (sym ∙ EQ) LT


module _ {o ℓ} {S : StrictPoset o ℓ} where
  open StrictPoset S

  dec-strict-total-order→tri-order
    : is-decidable-strict-total-order S
    → is-trichotomous S
  dec-strict-total-order→tri-order d .is-trichotomous.trisect x y
    with d .is-decidable-strict-total-order.has-discrete {x} {y}
  ... | yes x=y = EQ x=y
  ... | no  x≠y with d .is-decidable-strict-total-order.dec-< {x} {y}
  ... | yes x<y = LT x<y
  ... | no  x≮y with d .is-decidable-strict-total-order.dec-< {y} {x}
  ... | yes y<x = GT y<x
  ... | no  y≮x = ⊥.rec (x≠y (d .is-decidable-strict-total-order.connex x y x≮y y≮x))

  module _ (t : is-trichotomous S) where

    tri-order→strict-total-order : is-strict-total-order S
    tri-order→strict-total-order .is-strict-total-order.weak-linear x y z x<z =
      Tri.elim inl (λ x=y → inr (subst (_< z) x=y x<z)) (λ y<x → inr (y<x ∙ x<z))
        (t .is-trichotomous.trisect x y)
    tri-order→strict-total-order .is-strict-total-order.connex x y x≮y y≮x =
      Tri.elim (λ x<y → ⊥.rec (x≮y x<y)) refl (λ y<x → ⊥.rec (y≮x y<x))
        (t .is-trichotomous.trisect x y)

    tri-order→dec-strict-poset : is-decidable-strict-poset S
    tri-order→dec-strict-poset {x} {y} =
      Tri.elim yes (λ x=y → no $ =→≮ x=y) (λ y<x → no (<-asym y<x))
        (t .is-trichotomous.trisect x y)

    tri-order→discrete : is-discrete Ob
    tri-order→discrete {x} {y} =
      Tri.elim (λ x<y → no $ <→≠ x<y) yes (λ y<x → no λ x=y → <→≠ y<x (sym x=y))
        (t .is-trichotomous.trisect x y)

    tri-order→dec-strict-total-order : is-decidable-strict-total-order S
    tri-order→dec-strict-total-order
      .is-decidable-strict-total-order.has-is-strict-total = tri-order→strict-total-order
    tri-order→dec-strict-total-order
      .is-decidable-strict-total-order.dec-< = tri-order→dec-strict-poset
    tri-order→dec-strict-total-order
      .is-decidable-strict-total-order.has-discrete = tri-order→discrete



module _ {o ℓ} {S : StrictPoset o ℓ} ⦃ t : is-trichotomous S ⦄ where
  open is-trichotomous t

  private variable A : 𝒰 ℓ

  caseᵗ_>=<_of_ : (x y : Ob) → (Tri _<_ x y → A) → A
  caseᵗ_>=<_of_ x y f = f (trisect x y)
  {-# INLINE caseᵗ_>=<_of_ #-}

  caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ : (x y : Ob)
                         → A → A → A → A
  caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ x y l e g = Tri.rec l e g (trisect x y)
  {-# INLINE caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ #-}

  caseᵗ_>=<_return_of_ : (x y : Ob) (A : Tri _<_ x y → 𝒰 ℓ)
                       → (∀ t → A t) → A (trisect x y)
  caseᵗ_>=<_return_of_ x y A f = f (trisect x y)
  {-# INLINE caseᵗ_>=<_of_ #-}

  given-lt_return_then_ : {x y : Ob}
                        → (x<y : x < y)
                        → (A : Tri _<_ x y → 𝒰 ℓ)
                        → A (LT x<y)
                        → A (trisect x y)
  given-lt_return_then_ {x} {y} x<y A alt = Tri.elim {M = A}
    (λ x<y′ → subst A (ap LT prop!) alt)
    (λ x=y → ⊥.rec (=→≮ x=y x<y))
    (λ y<x → ⊥.rec (<-asym x<y y<x))
    (trisect x y)

  given-eq_return_then_ : {x y : Ob}
                        → (x=y : x ＝ y)
                        → (A : Tri _<_ x y → 𝒰 ℓ)
                        → A (EQ x=y)
                        → A (trisect x y)
  given-eq_return_then_ {x} {y} x=y A aeq = Tri.elim {M = A}
    (λ x<y → ⊥.rec (=→≮ x=y x<y))
    (λ p → subst A (ap EQ (path-is-of-hlevel 1 (is-discrete→is-set (tri-order→discrete t)) x y x=y p)) aeq)
    (λ y<x → ⊥.rec (=→≮ (sym x=y) y<x))
    (trisect x y)

  given-gt_return_then_ : {x y : Ob}
                        → (y<x : y < x)
                        → (A : Tri _<_ x y → 𝒰 ℓ)
                        → A (GT y<x)
                        → A (trisect x y)
  given-gt_return_then_ {x} {y} y<x A agt = Tri.elim {M = A}
    (λ x<y → ⊥.rec (<-asym x<y y<x))
    (λ x=y → ⊥.rec (<→≠ y<x (sym x=y)))
    (λ gt → subst A (ap GT prop!) agt)
    (trisect x y)
