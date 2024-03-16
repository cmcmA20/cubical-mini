{-# OPTIONS --safe #-}
module Algebra.Rig.Commutative.Category where

open import Algebra.Rig.Commutative
open import Algebra.Rig.Category.Base using (Rig-structure; Rigs)

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude
import Categories.Morphism

open Semiring-hom
open CRig-on

CRig-structure : ∀ ℓ → Thin-structure ℓ CRig-on
CRig-structure ℓ = Full-substructure ℓ CRig-on Rig-on
  (λ _ → comm-rig-on↪rig-on) (Rig-structure ℓ)

CRigs : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
CRigs ℓ = Structured-objects (CRig-structure ℓ)

module CRigs {ℓ} = Categories.Morphism (CRigs ℓ)

CRig : ∀ ℓ → 𝒰 (ℓsuc ℓ)
CRig ℓ = Precategory.Ob (CRigs ℓ)

private variable ℓ : Level

instance
  CRigs-equational : is-equational (Rig-structure ℓ)
  CRigs-equational .invert-id-hom p .pres-0 = p .pres-0 ⁻¹
  CRigs-equational .invert-id-hom p .pres-1 = p .pres-1 ⁻¹
  CRigs-equational .invert-id-hom p .pres-+ _ _ = p .pres-+ _ _ ⁻¹
  CRigs-equational .invert-id-hom p .pres-· _ _ = p .pres-· _ _ ⁻¹

Forget : Functor (CRigs ℓ) (Sets ℓ)
Forget = Forget-structure (CRig-structure _)

Forget-comm : Functor (CRigs ℓ) (Rigs ℓ)
Forget-comm .Functor.F₀ = second (comm-rig-on↪rig-on $_)
Forget-comm .Functor.F₁ f .hom = f $_
Forget-comm .Functor.F₁ f .preserves = f .preserves
Forget-comm .Functor.F-id = reflₚ
Forget-comm .Functor.F-∘ _ _ = reflₚ

forget-comm-is-faithful : is-faithful (Forget-comm {ℓ})
forget-comm-is-faithful p = ext $ p $ₚ_
