{-# OPTIONS --safe #-}
module Algebra.Group.Category where

open import Algebra.Group
open import Algebra.Monoid.Category using (Monoids)

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude
import Categories.Morphism

open Group-hom
open Group-on

Group-structure : ∀ ℓ → Thin-structure ℓ Group-on
Group-structure ℓ .is-hom f A B = el! (Group-hom A B f)
Group-structure ℓ .id-is-hom .pres-⋆ _ _ = refl
Group-structure ℓ .∘-is-hom f g p q .pres-⋆ _ _ =
  ap f (q .pres-⋆ _ _) ∙ p .pres-⋆ _ _
Group-structure ℓ .id-hom-unique p q .erased = Equiv.injective
  (≅ₜ→≃ group-on-iso) $ Σ-prop-path! $ ext $ p .pres-⋆

Groups : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Groups ℓ = Structured-objects (Group-structure ℓ)

module Groups {ℓ} = Categories.Morphism (Groups ℓ)

Group : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Group ℓ = Precategory.Ob (Groups ℓ)

private variable ℓ : Level

instance
  Groups-equational : is-equational (Group-structure ℓ)
  Groups-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : Functor (Groups ℓ) (Sets ℓ)
Forget = Forget-structure (Group-structure _)

Forget-inverse : Functor (Groups ℓ) (Monoids ℓ)
Forget-inverse .Functor.F₀ = second (group-on↪monoid-on $_)
Forget-inverse .Functor.F₁ f .hom = f $_
Forget-inverse .Functor.F₁ f .preserves .Monoid-hom.pres-id =
  pres-id (f .preserves)
Forget-inverse .Functor.F₁ f .preserves .Monoid-hom.pres-⋆ =
  f .preserves .pres-⋆
Forget-inverse .Functor.F-id = trivial!
Forget-inverse .Functor.F-∘ _ _ = trivial!

forget-inverse-is-faithful : is-faithful (Forget-inverse {ℓ})
forget-inverse-is-faithful p = ext $ p $ₚ_
