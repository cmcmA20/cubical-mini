{-# OPTIONS --safe #-}
module Algebra.Magma.Category where

open import Algebra.Magma

open import Cat.Prelude
open import Cat.Constructions.Types
open import Cat.Displayed.Univalence.Thin
import Cat.Morphism

open n-Magma-on
open n-Magma-hom

Magma-structure : ∀ ℓ → Thin-structure (Types ℓ) ℓ Magma-on
Magma-structure ℓ .is-hom f A B = el! (n-Magma-hom 2 f A B)
Magma-structure ℓ .id-is-hom .pres-⋆ _ _ = refl
Magma-structure ℓ .∘-is-hom f g p q .pres-⋆ a b =
  ap f (q .pres-⋆ _ _) ∙ pres-⋆ p _ _
Magma-structure ℓ .id-hom-unique p _ = pure $ Equiv.injective
  (≅ₜ→≃ $ n-magma-on-iso 2) $ ext # p .pres-⋆ ,ₚ prop!

Magmas : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Magmas ℓ = Structured-objects (Magma-structure ℓ)

module Magmas {ℓ} = Cat.Morphism (Magmas ℓ)

Magma : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Magma ℓ = Precategory.Ob (Magmas ℓ)

private variable ℓ : Level

@0 Magmas-is-category : ∀ {ℓ} → is-category (Magmas ℓ)
Magmas-is-category = Structured-objects-is-category (Magma-structure _) auto

instance
  Magmas-equational : is-equational (Magma-structure ℓ)
  Magmas-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : Magmas ℓ ⇒ Types ℓ
Forget = Forget-structure (Magma-structure _)
