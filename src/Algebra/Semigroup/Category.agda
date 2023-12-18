{-# OPTIONS --safe #-}
module Algebra.Semigroup.Category where

open import Algebra.Magma.Category using (Magma-structure; Magmas)
open import Algebra.Semigroup

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude

open n-Magma-hom
open Semigroup-on

Semigroup-structure : ∀ ℓ → Thin-structure ℓ Semigroup-on
Semigroup-structure ℓ .is-hom f A B =
  el! (n-Magma-hom 2 (semigroup→magma A) (semigroup→magma B) f)
Semigroup-structure ℓ .id-is-hom = Magma-structure ℓ .id-is-hom
Semigroup-structure ℓ .∘-is-hom = Magma-structure ℓ .∘-is-hom
Semigroup-structure ℓ .id-hom-unique p _ = Equiv.injective
  (isoₜ→equiv semigroup-on-iso) $ Σ-prop-path! $ ext $ p .pres-⋆

Semigroups : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Semigroups ℓ = Structured-objects (Semigroup-structure ℓ)

private variable ℓ : Level

instance
  Semigroups-equational : is-equational (Semigroup-structure ℓ)
  Semigroups-equational .invert-id-hom p .pres-⋆ _ _ = sym (p .pres-⋆ _ _)

Forget : Functor (Semigroups ℓ) (Sets ℓ)
Forget = Forget-structure (Semigroup-structure _)

Forget-assoc : Functor (Semigroups ℓ) (Magmas ℓ)
Forget-assoc .Functor.F₀ = second semigroup→magma
Forget-assoc .Functor.F₁ f .hom x = f # x
Forget-assoc .Functor.F₁ f .preserves = f .preserves
Forget-assoc .Functor.F-id = refl
Forget-assoc .Functor.F-∘ _ _ = refl

forget-assoc-is-faithful : is-faithful (Forget-assoc {ℓ})
forget-assoc-is-faithful p i .hom = p i .hom
forget-assoc-is-faithful p i .preserves = p i .preserves
