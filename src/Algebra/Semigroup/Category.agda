{-# OPTIONS --safe #-}
module Algebra.Semigroup.Category where

open import Algebra.Magma.Category using (Magma-structure; Magmas)
open import Algebra.Semigroup

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude
import Categories.Morphism

open n-Magma-hom
open Semigroup-on

Semigroup-structure : ∀ ℓ → Thin-structure ℓ Semigroup-on
Semigroup-structure ℓ = Full-substructure ℓ Semigroup-on Magma-on
  (λ _ → semigroup-on↪magma-on) (Magma-structure ℓ)

Semigroups : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Semigroups ℓ = Structured-objects (Semigroup-structure ℓ)

module Semigroups {ℓ} = Categories.Morphism (Semigroups ℓ)

Semigroup : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Semigroup ℓ = Precategory.Ob (Semigroups ℓ)

private variable ℓ : Level

instance
  Semigroups-equational : is-equational (Semigroup-structure ℓ)
  Semigroups-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : Functor (Semigroups ℓ) (Sets ℓ)
Forget = Forget-structure (Semigroup-structure _)

Forget-assoc : Functor (Semigroups ℓ) (Magmas ℓ)
Forget-assoc .Functor.F₀ = second (semigroup-on↪magma-on $_)
Forget-assoc .Functor.F₁ f .hom = f $_
Forget-assoc .Functor.F₁ f .preserves = f .preserves
Forget-assoc .Functor.F-id = reflₚ
Forget-assoc .Functor.F-∘ _ _ = reflₚ

forget-assoc-is-faithful : is-faithful (Forget-assoc {ℓ})
forget-assoc-is-faithful p = ext $ p $ₚ_
