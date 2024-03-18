{-# OPTIONS --safe #-}
module Algebra.Group.Abelian.Category where

open import Algebra.Group.Category using (Group-structure; Groups)
open import Algebra.Group.Abelian

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude
import Categories.Morphism

open Group-hom
open AGroup-on

AGroup-structure : ∀ ℓ → Thin-structure ℓ AGroup-on
AGroup-structure ℓ = Full-substructure ℓ AGroup-on Group-on
  (λ _ → abelian-group-on↪group-on) (Group-structure ℓ)

AGroups : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
AGroups ℓ = Structured-objects (AGroup-structure ℓ)

module AGroups {ℓ} = Categories.Morphism (AGroups ℓ)

AGroup : ∀ ℓ → 𝒰 (ℓsuc ℓ)
AGroup ℓ = Precategory.Ob (AGroups ℓ)

private variable ℓ : Level

instance
  AGroups-equational : is-equational (AGroup-structure ℓ)
  AGroups-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : Functor (AGroups ℓ) (Sets ℓ)
Forget = Forget-structure (AGroup-structure _)

Forget-comm : Functor (AGroups ℓ) (Groups ℓ)
Forget-comm .Functor.F₀ = second (abelian-group-on↪group-on $_)
Forget-comm .Functor.F₁ f .hom = f $_
Forget-comm .Functor.F₁ f .preserves = f .preserves
Forget-comm .Functor.F-id = refl
Forget-comm .Functor.F-∘ _ _ = refl

forget-comm-is-faithful : is-faithful (Forget-comm {ℓ})
forget-comm-is-faithful p = ext $ p $ₚ_
