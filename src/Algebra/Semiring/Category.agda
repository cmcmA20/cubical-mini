{-# OPTIONS --safe #-}
module Algebra.Semiring.Category where

open import Algebra.Semiring

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude

open Semiring-hom
open Semiring-on

Semiring-structure : ∀ ℓ → Thin-structure ℓ Semiring-on
Semiring-structure ℓ .is-hom f A B = el! (Semiring-hom A B f)
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
Semiring-structure ℓ .id-hom-unique p q = Equiv.injective
  (isoₜ→equiv semiring-on-iso) $ Σ-pathP (p .pres-0) $
    Σ-pathP (p .pres-1) $ Σ-pathP (ext (p .pres-+)) $
      Σ-prop-pathP hlevel! (ext (p .pres-·))

Semirings : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Semirings ℓ = Structured-objects (Semiring-structure ℓ)

private variable ℓ : Level

instance
  Semirings-equational : is-equational (Semiring-structure ℓ)
  Semirings-equational .invert-id-hom p .pres-0 = sym (p .pres-0)
  Semirings-equational .invert-id-hom p .pres-1 = sym (p .pres-1)
  Semirings-equational .invert-id-hom p .pres-+ _ _ = sym (p .pres-+ _ _)
  Semirings-equational .invert-id-hom p .pres-· _ _ = sym (p .pres-· _ _)

Forget : Functor (Semirings ℓ) (Sets ℓ)
Forget = Forget-structure (Semiring-structure _)
