{-# OPTIONS --safe #-}
module Algebra.Semiring.Category where

open import Algebra.Semiring

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude
import Cat.Morphism

open Semiring-hom
open Semiring-on

Semiring-structure : ∀ ℓ → Thin-structure ℓ Semiring-on
Semiring-structure ℓ .is-hom f A B = el! (Semiring-hom f A B)
Semiring-structure ℓ .id-is-hom .pres-0 = refl
Semiring-structure ℓ .id-is-hom .pres-1 = refl
Semiring-structure ℓ .id-is-hom .pres-+ _ _ = refl
Semiring-structure ℓ .id-is-hom .pres-· _ _ = refl
Semiring-structure ℓ .∘-is-hom f g p q .pres-0 =
  ap f (q .pres-0) ∙ p .pres-0
Semiring-structure ℓ .∘-is-hom f g p q .pres-1 =
  ap f (q .pres-1) ∙ p .pres-1
Semiring-structure ℓ .∘-is-hom f g p q .pres-+ _ _ =
  ap f (q .pres-+ _ _) ∙ p .pres-+ _ _
Semiring-structure ℓ .∘-is-hom f g p q .pres-· _ _ =
  ap f (q .pres-· _ _) ∙ p .pres-· _ _
Semiring-structure ℓ .id-hom-unique p q .erased = Equiv.injective (≅ₜ→≃ semiring-on-iso)
  $ ext (p .pres-+) ,ₚ ext (p .pres-·) ,ₚ prop!

Semirings : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Semirings ℓ = Structured-objects (Semiring-structure ℓ)

module Semirings {ℓ} = Cat.Morphism (Semirings ℓ)

Semiring : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Semiring ℓ = Precategory.Ob (Semirings ℓ)

private variable ℓ : Level

instance
  Semirings-equational : is-equational (Semiring-structure ℓ)
  Semirings-equational .invert-id-hom p .pres-0 = sym (p .pres-0)
  Semirings-equational .invert-id-hom p .pres-1 = sym (p .pres-1)
  Semirings-equational .invert-id-hom p .pres-+ _ _ = sym (p .pres-+ _ _)
  Semirings-equational .invert-id-hom p .pres-· _ _ = sym (p .pres-· _ _)

Forget : Semirings ℓ ⇒ Sets ℓ
Forget = Forget-structure (Semiring-structure _)
