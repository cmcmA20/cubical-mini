{-# OPTIONS --safe #-}
module Algebra.Monoid.Commutative.Category where

open import Algebra.Monoid.Category using (Monoid-structure; Monoids)
open import Algebra.Monoid.Commutative

open import Cat.Functor.Properties
open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude
import Cat.Morphism

open Monoid-hom
open CMonoid-on

CMonoid-structure : ∀ ℓ → Thin-structure (Types ℓ) ℓ CMonoid-on
CMonoid-structure ℓ = Full-substructure ℓ CMonoid-on Monoid-on
  (λ _ → comm-monoid-on↪monoid-on) (Monoid-structure ℓ)

CMonoids : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
CMonoids ℓ = Structured-objects (CMonoid-structure ℓ)

module CMonoids {ℓ} = Cat.Morphism (CMonoids ℓ)

CMonoid : ∀ ℓ → 𝒰 (ℓsuc ℓ)
CMonoid ℓ = Precategory.Ob (CMonoids ℓ)

private variable ℓ : Level

instance
  CMonoids-equational : is-equational (CMonoid-structure ℓ)
  CMonoids-equational .invert-id-hom p .pres-id = p .pres-id ⁻¹
  CMonoids-equational .invert-id-hom p .pres-⋆ _ _ = p .pres-⋆ _ _ ⁻¹

Forget : CMonoids ℓ ⇒ Types ℓ
Forget = Forget-structure (CMonoid-structure _)

Forget-comm : CMonoids ℓ ⇒ Monoids ℓ
Forget-comm .Functor.F₀ = second (comm-monoid-on↪monoid-on $_)
Forget-comm .Functor.F₁ f .hom x = f $ x
Forget-comm .Functor.F₁ f .preserves = f .preserves
Forget-comm .Functor.F-id = refl
Forget-comm .Functor.F-∘ _ _ = refl

forget-comm-is-faithful : is-faithful (Forget-comm {ℓ})
forget-comm-is-faithful p = ext (p $ₚ_)
