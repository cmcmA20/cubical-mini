{-# OPTIONS --safe #-}
module Algebra.Magma.Unital.Category where

open import Algebra.Magma.Category using (Magma-structure; Magmas)
open import Algebra.Magma.Unital

open import Cat.Functor.Properties
open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude
import Cat.Morphism

open n-Magma-hom
open UMagma-hom

UMagma-structure : ∀ ℓ → Thin-structure (Types ℓ) ℓ UMagma-on
UMagma-structure ℓ .is-hom f A B = el! (UMagma-hom f A B)
UMagma-structure ℓ .id-is-hom .pres-id = refl
UMagma-structure ℓ .id-is-hom .pres-⋆ _ _ = refl
UMagma-structure ℓ .∘-is-hom f g p q .pres-id =
  ap f (q .pres-id) ∙ p .pres-id
UMagma-structure ℓ .∘-is-hom f g p q .pres-⋆ _ _ =
  ap f (q .pres-⋆ _ _) ∙ p .pres-⋆ _ _
UMagma-structure ℓ .id-hom-unique p q .erased = Equiv.injective
  (≅ₜ→≃ umagma-on-iso) $ Σ-prop-path! $ ext (p .pres-⋆)

UMagmas : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
UMagmas ℓ = Structured-objects (UMagma-structure ℓ)

module UMagmas {ℓ} = Cat.Morphism (UMagmas ℓ)

UMagma : ∀ ℓ → 𝒰 (ℓsuc ℓ)
UMagma ℓ = Precategory.Ob (UMagmas ℓ)

private variable ℓ : Level

instance
  UMagmas-equational : is-equational (UMagma-structure ℓ)
  UMagmas-equational .invert-id-hom p .pres-id = p .pres-id ⁻¹
  UMagmas-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : UMagmas ℓ ⇒ Types ℓ
Forget = Forget-structure (UMagma-structure _)

Forget-unit : UMagmas ℓ ⇒ Magmas ℓ
Forget-unit .Functor.F₀ = second (unital-magma-on↪magma-on $_)
Forget-unit .Functor.F₁ f .hom x = f $ x
Forget-unit .Functor.F₁ f .preserves .pres-⋆ = f .preserves .pres-⋆
Forget-unit .Functor.F-id = trivial!
Forget-unit .Functor.F-∘ _ _ = trivial!

forget-unit-is-faithful : is-faithful (Forget-unit {ℓ})
forget-unit-is-faithful p = ext (p $ₚ_)
