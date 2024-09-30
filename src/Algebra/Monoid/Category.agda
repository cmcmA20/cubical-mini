{-# OPTIONS --safe #-}
module Algebra.Monoid.Category where

open import Algebra.Magma.Unital.Category using (UMagmas)
open import Algebra.Monoid
open import Algebra.Semigroup.Category using (Semigroups)

open import Cat.Functor.Properties
open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude
import Cat.Morphism

open Monoid-hom
open Monoid-on

Monoid-structure : ∀ ℓ → Thin-structure ℓ Monoid-on
Monoid-structure ℓ .is-hom f A B = el! (Monoid-hom f A B)
Monoid-structure ℓ .id-is-hom .pres-id = refl
Monoid-structure ℓ .id-is-hom .pres-⋆ _ _ = refl
Monoid-structure ℓ .∘-is-hom f g p q .pres-id =
  ap f (q .pres-id) ∙ p .pres-id
Monoid-structure ℓ .∘-is-hom f g p q .pres-⋆ _ _ =
  ap f (q .pres-⋆ _ _) ∙ p .pres-⋆ _ _
Monoid-structure ℓ .id-hom-unique p q .erased = Equiv.injective
  (≅ₜ→≃ monoid-on-iso) $ Σ-prop-path! $ ext (p .pres-⋆)

Monoids : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Monoids ℓ = Structured-objects (Monoid-structure ℓ)

module Monoids {ℓ} = Cat.Morphism (Monoids ℓ)

Monoid : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Monoid ℓ = Precategory.Ob (Monoids ℓ)

private variable ℓ : Level

instance
  Monoids-equational : is-equational (Monoid-structure ℓ)
  Monoids-equational .invert-id-hom p .pres-id = p .pres-id ⁻¹
  Monoids-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : Monoids ℓ ⇒ Types ℓ
Forget = Forget-structure (Monoid-structure _)

Forget-unit : Monoids ℓ ⇒ Semigroups ℓ
Forget-unit .Functor.F₀ = second (monoid-on↪semigroup-on $_)
Forget-unit .Functor.F₁ f .hom x = f $ x
Forget-unit .Functor.F₁ f .preserves .n-Magma-hom.pres-⋆ =
  f .preserves .pres-⋆
Forget-unit .Functor.F-id = ext λ _ → refl
Forget-unit .Functor.F-∘ _ _ = ext λ _ → refl

forget-unit-is-faithful : is-faithful (Forget-unit {ℓ})
forget-unit-is-faithful p = ext (p $ₚ_)


Forget-assoc : Monoids ℓ ⇒ UMagmas ℓ
Forget-assoc .Functor.F₀ = second (monoid-on↪unital-magma-on $_)
Forget-assoc .Functor.F₁ f .hom = f $_
Forget-assoc .Functor.F₁ f .preserves .UMagma-hom.pres-id =
  f .preserves .pres-id
Forget-assoc .Functor.F₁ f .preserves .UMagma-hom.pres-⋆ =
  f .preserves .pres-⋆
Forget-assoc .Functor.F-id = ext λ _ → refl
Forget-assoc .Functor.F-∘ _ _ = ext λ _ → refl

forget-assoc-is-faithful : is-faithful (Forget-assoc {ℓ})
forget-assoc-is-faithful p = ext (p $ₚ_)
