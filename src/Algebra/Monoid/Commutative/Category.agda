{-# OPTIONS --safe #-}
module Algebra.Monoid.Commutative.Category where

open import Algebra.Monoid.Category using (Monoid-structure; Monoids)
open import Algebra.Monoid.Commutative

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude

open Monoid-hom
open CMonoid-on

CMonoid-structure : ∀ ℓ → Thin-structure ℓ CMonoid-on
CMonoid-structure ℓ .is-hom f A B =
  el! (Monoid-hom (comm-monoid→monoid A) (comm-monoid→monoid B) f)
CMonoid-structure ℓ .id-is-hom = Monoid-structure ℓ .id-is-hom
CMonoid-structure ℓ .∘-is-hom = Monoid-structure ℓ .∘-is-hom
CMonoid-structure ℓ .id-hom-unique p _ = Equiv.injective
  (isoₜ→equiv cmonoid-on-iso) $ Σ-pathP (ext (p .pres-id)) $
    Σ-prop-pathP hlevel! (ext (p .pres-⋆))

CMonoids : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
CMonoids ℓ = Structured-objects (CMonoid-structure ℓ)

private variable ℓ : Level

instance
  CMonoids-equational : is-equational (CMonoid-structure ℓ)
  CMonoids-equational .invert-id-hom p .pres-id = sym (p .pres-id)
  CMonoids-equational .invert-id-hom p .pres-⋆ _ _ = sym (p .pres-⋆ _ _)

Forget : Functor (CMonoids ℓ) (Sets ℓ)
Forget = Forget-structure (CMonoid-structure _)

Forget-comm : Functor (CMonoids ℓ) (Monoids ℓ)
Forget-comm .Functor.F₀ = second comm-monoid→monoid
Forget-comm .Functor.F₁ f .hom x = f # x
Forget-comm .Functor.F₁ f .preserves = f .preserves
Forget-comm .Functor.F-id = refl
Forget-comm .Functor.F-∘ _ _ = refl

forget-comm-is-faithful : is-faithful (Forget-comm {ℓ})
forget-comm-is-faithful p i .hom = p i .hom
forget-comm-is-faithful p i .preserves = p i .preserves
