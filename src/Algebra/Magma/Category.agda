{-# OPTIONS --safe #-}
module Algebra.Magma.Category where

open import Algebra.Magma

open import Categories.Prelude
open import Categories.Displayed.Univalence.Thin
import Categories.Morphism

open n-Magma-on
open n-Magma-hom

Magma-structure : ∀ ℓ → Thin-structure ℓ Magma-on
Magma-structure ℓ .is-hom f A B = el! (n-Magma-hom 2 A B f)
Magma-structure ℓ .id-is-hom .pres-⋆ _ _ = reflₚ
Magma-structure ℓ .∘-is-hom f g p q .pres-⋆ a b =
  ap f (q .pres-⋆ _ _) ∙ pres-⋆ p _ _
Magma-structure ℓ .id-hom-unique p _ = pure $ Equiv.injective
  (isoₜ→equiv $ n-magma-on-iso 2) $ Σ-prop-path! $ ext $ p .pres-⋆

Magmas : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Magmas ℓ = Structured-objects (Magma-structure ℓ)

module Magmas {ℓ} = Categories.Morphism (Magmas ℓ)

Magma : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Magma ℓ = Precategory.Ob (Magmas ℓ)

private variable ℓ : Level

-- TODO univalent version
-- Magmas-is-category : ∀ {ℓ} → is-category (Magmas ℓ)
-- Magmas-is-category = Structured-objects-is-category (Magma-structure _)

instance
  Magmas-equational : is-equational (Magma-structure ℓ)
  Magmas-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : Functor (Magmas ℓ) (Sets ℓ)
Forget = Forget-structure (Magma-structure _)
