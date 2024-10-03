{-# OPTIONS --safe #-}
module Order.Trichotomous where

open import Cat.Prelude

open import Order.Strict
open import Order.Total

open import Data.Dec
open import Data.Sum
open import Data.Sum.Exclusive.Tri as Tri

pattern lt x<y x≠y x≯y = inxl x<y x≠y x≯y
pattern eq x≮y x=y x≯y = inxm x≮y x=y x≯y
pattern gt x≮y x≠y x>y = inxr x≮y x≠y x>y

record is-trichotomous {o ℓ} (S : StrictPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  open StrictPoset S public

  Tri< : ∀ x y → 𝒰 (o ⊔ ℓ)
  Tri< x y = Tri (x < y) (x ＝ y) (x > y)

  field trisect : ∀ x y → Tri< x y

  instance
    Refl-Tri< : Refl Tri<
    Refl-Tri< .refl = eq <-irrefl refl <-irrefl

    Sym-Tri< : Sym Tri<
    Sym-Tri< ._ᵒᵖ = Tri.elim
      (λ x<y x≠y x≯y → gt x≯y (sym ∙ x≠y) x<y)
      (λ x≮y x=y x≯y → eq x≯y (sym x=y) x≮y)
      (λ x≮y x≠y x>y → lt x>y (sym ∙ x≠y) x≮y)


module _ {o ℓ} {S : StrictPoset o ℓ} where
  open StrictPoset S

  dec-strict-total-order→tri-order
    : is-decidable-strict-total-order S
    → is-trichotomous S
  dec-strict-total-order→tri-order d .is-trichotomous.trisect x y
    with d .is-decidable-strict-total-order.has-discrete {x} {y}
  ... | yes x=y = eq (λ x<y → <→≠ x<y x=y) x=y (λ y<x → =→≮ (x=y ⁻¹) y<x)
  ... | no x≠y with d .is-decidable-strict-total-order.dec-< {x} {y}
  ...          | yes x<y = lt x<y x≠y (<-asym x<y)
  ...          | no x≮y with d .is-decidable-strict-total-order.dec-< {y} {x}
  ...                   | yes y<x = gt x≮y x≠y y<x
  ...                   | no  y≮x = ⊥.rec (x≠y (d .is-decidable-strict-total-order.connex x y x≮y y≮x))

  module _ (t : is-trichotomous S) where

    tri-order→strict-total-order : is-strict-total-order S
    tri-order→strict-total-order .is-strict-total-order.weak-linear x y z x<z =
      Tri.elim (λ x<y x≠y y≮x → inl x<y)
               (λ x≮y x=y y≮x → inr (subst (_< z) x=y x<z))
               (λ x≮y x≠y y<x → inr (y<x ∙ x<z))
               (t .is-trichotomous.trisect x y)
    tri-order→strict-total-order .is-strict-total-order.connex x y x≮y y≮x =
      Tri.elim (λ x<y _ _ → ⊥.rec (x≮y x<y))
               (λ _ x=y _ → x=y)
               (λ _ _ y<x → ⊥.rec (y≮x y<x))
               (t .is-trichotomous.trisect x y)

    tri-order→dec-strict-poset : is-decidable-strict-poset S
    tri-order→dec-strict-poset {x} {y} = tri→dec-l (t .is-trichotomous.trisect x y)

    tri-order→discrete : is-discrete Ob
    tri-order→discrete {x} {y} = tri→dec-m (t .is-trichotomous.trisect x y)

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

  caseᵗ_>=<_of_ : (x y : Ob) → (Tri< x y → A) → A
  caseᵗ_>=<_of_ x y f = f (trisect x y)
  {-# INLINE caseᵗ_>=<_of_ #-}

  caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ : (x y : Ob)
                         → A → A → A → A
  caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ x y l e g = Tri.rec l e g (trisect x y)
  {-# INLINE caseᵗ_>=<_lt⇒_eq⇒_gt⇒_ #-}

  caseᵗ_>=<_return_of_ : (x y : Ob) (A : Tri< x y → 𝒰 ℓ)
                       → (∀ t → A t) → A (trisect x y)
  caseᵗ_>=<_return_of_ x y A f = f (trisect x y)
  {-# INLINE caseᵗ_>=<_of_ #-}

  given-lt_return_then_ : {x y : Ob}
                        → (x<y : x < y)
                        → (A : Tri< x y → 𝒰 ℓ)
                        → A (lt x<y (<→≠ x<y) (<-asym x<y))
                        → A (trisect x y)
  given-lt_return_then_ {x} {y} x<y A alt =
    Tri.elim {M = A}
      (λ x<y′ x≠y y≮x →
         subst (λ q → A (lt q x≠y y≮x)) prop! $
         subst (λ q → A (lt x<y q y≮x)) prop! $
         subst (λ q → A (lt x<y (<→≠ x<y) q)) prop! alt)
      (λ _ x=y _ → ⊥.rec (<→≠ x<y x=y))
      (λ x≮y _ _ → ⊥.rec (x≮y x<y))
      (trisect x y)

  given-eq_return_then_ : {x y : Ob}
                        → (x=y : x ＝ y)
                        → (A : Tri< x y → 𝒰 ℓ)
                        → A (eq (=→≮ x=y) x=y (=→≮ $ x=y ⁻¹))
                        → A (trisect x y)
  given-eq_return_then_ {x} {y} x=y A aeq =
    Tri.elim {M = A}
      (λ _ x≠y _ → ⊥.rec (x≠y x=y))
      (λ x≮y x=y′ y≮x →
       subst (λ q → A (eq q x=y′ y≮x)) prop! $
       subst (λ q → A (eq (=→≮ x=y) q y≮x)) (path-is-of-hlevel 1 (is-discrete→is-set (tri-order→discrete t)) x y x=y x=y′) $
       subst (λ q → A (eq (=→≮ x=y) x=y q)) prop! aeq)
      (λ _ x≠y _ → ⊥.rec (x≠y x=y))
      (trisect x y)

  given-gt_return_then_ : {x y : Ob}
                        → (y<x : y < x)
                        → (A : Tri< x y → 𝒰 ℓ)
                        → A (gt (<-asym y<x) (<→≠ y<x ∘ₜ _⁻¹) y<x)
                        → A (trisect x y)
  given-gt_return_then_ {x} {y} y<x A agt =
    Tri.elim {M = A}
      (λ _ _ y≮x → ⊥.rec (y≮x y<x))
      (λ _ x=y _ → ⊥.rec (<→≠ y<x (x=y ⁻¹)))
      (λ x≮y x≠y y<x′ →
        subst (λ q → A (gt q x≠y y<x′)) prop! $
        subst (λ q → A (gt (<-asym y<x) q y<x′)) prop! $
        subst (λ q → A (gt (<-asym y<x) (<→≠ y<x ∘ₜ _⁻¹) q)) prop! agt)
      (trisect x y)
