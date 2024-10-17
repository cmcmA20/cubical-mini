{-# OPTIONS --safe #-}
module Algebra.Group.Category where

open import Algebra.Group
open import Algebra.Monoid.Category using (Monoids)

open import Cat.Functor.Properties
open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude
import Cat.Morphism

open Group-hom
open Group-on

Group-structure : ∀ ℓ → Thin-structure ℓ Group-on
Group-structure ℓ .is-hom f A B = el! (Group-hom f A B)
Group-structure ℓ .id-is-hom .pres-⋆ _ _ = refl
Group-structure ℓ .∘-is-hom f g p q .pres-⋆ _ _ =
  ap f (q .pres-⋆ _ _) ∙ p .pres-⋆ _ _
Group-structure ℓ .id-hom-unique p q .erased = Equiv.injective
  (≅ₜ→≃ group-on-iso) $ ext (p .pres-⋆) ,ₚ prop!

Groups : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Groups ℓ = Structured-objects (Group-structure ℓ)

module Groups {ℓ} = Cat.Morphism (Groups ℓ)

Group : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Group ℓ = Precategory.Ob (Groups ℓ)

private variable ℓ : Level

instance
  Groups-equational : is-equational (Group-structure ℓ)
  Groups-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : Groups ℓ ⇒ Types ℓ
Forget = Forget-structure (Group-structure _)

Forget-inverse : Groups ℓ ⇒ Monoids ℓ
Forget-inverse .Functor.F₀ = second (group-on↪monoid-on $_)
Forget-inverse .Functor.F₁ f .hom = f $_
Forget-inverse .Functor.F₁ f .preserves .Monoid-hom.pres-id =
  pres-id (f .preserves)
Forget-inverse .Functor.F₁ f .preserves .Monoid-hom.pres-⋆ =
  f .preserves .pres-⋆
Forget-inverse .Functor.F-id = trivial!
Forget-inverse .Functor.F-∘ _ _ = trivial!

forget-inverse-is-faithful : is-faithful (Forget-inverse {ℓ})
forget-inverse-is-faithful p = ext (p $ₚ_)
