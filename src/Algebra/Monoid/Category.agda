{-# OPTIONS --safe #-}
module Algebra.Monoid.Category where

open import Algebra.Monoid
open import Algebra.Semigroup.Category using (Semigroups)

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude
import Categories.Morphism

open Monoid-hom
open Monoid-on

Monoid-structure : ∀ ℓ → Thin-structure ℓ Monoid-on
Monoid-structure ℓ .is-hom f A B = el! (Monoid-hom A B f)
Monoid-structure ℓ .id-is-hom .pres-id = refl
Monoid-structure ℓ .id-is-hom .pres-⋆ _ _ = refl
Monoid-structure ℓ .∘-is-hom f g p q .pres-id =
  ap f (q .pres-id) ∙ p .pres-id
Monoid-structure ℓ .∘-is-hom f g p q .pres-⋆ _ _ =
  ap f (q .pres-⋆ _ _) ∙ p .pres-⋆ _ _
Monoid-structure ℓ .id-hom-unique p q = Equiv.injective
  (isoₜ→equiv monoid-on-iso) $ Σ-pathP (p .pres-id) $
    Σ-prop-pathP hlevel! (ext (p .pres-⋆))

Monoids : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Monoids ℓ = Structured-objects (Monoid-structure ℓ)

module Monoids {ℓ} = Categories.Morphism (Monoids ℓ)

Monoid : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Monoid ℓ = Precategory.Ob (Monoids ℓ)

private variable ℓ : Level

instance
  Monoids-equational : is-equational (Monoid-structure ℓ)
  Monoids-equational .invert-id-hom p .pres-id = sym (p .pres-id)
  Monoids-equational .invert-id-hom p .pres-⋆ _ _ = sym (p .pres-⋆ _ _)

Forget : Functor (Monoids ℓ) (Sets ℓ)
Forget = Forget-structure (Monoid-structure _)

Forget-neutral : Functor (Monoids ℓ) (Semigroups ℓ)
Forget-neutral .Functor.F₀ = second monoid-on→semigroup-on
Forget-neutral .Functor.F₁ f .hom x = f # x
Forget-neutral .Functor.F₁ f .preserves .n-Magma-hom.pres-⋆ =
  f .preserves .pres-⋆
Forget-neutral .Functor.F-id = trivial!
Forget-neutral .Functor.F-∘ _ _ = trivial!

forget-neutral-is-faithful : is-faithful (Forget-neutral {ℓ})
forget-neutral-is-faithful p =
  total-hom-path (Thin-structure-over _) (ext (p #ₚ_)) prop!
