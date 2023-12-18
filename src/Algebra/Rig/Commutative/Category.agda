{-# OPTIONS --safe #-}
module Algebra.Rig.Commutative.Category where

open import Algebra.Rig.Commutative
open import Algebra.Rig.Category.Base using (Rig-structure; Rigs)

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude

open Semiring-hom
open CRig-on

CRig-structure : ∀ ℓ → Thin-structure ℓ CRig-on
CRig-structure ℓ .is-hom f A B =
  el! (Semiring-hom (rig→semiring (comm-rig→rig A))
                    (rig→semiring (comm-rig→rig B)) f)
CRig-structure ℓ .id-is-hom = Rig-structure ℓ .id-is-hom
CRig-structure ℓ .∘-is-hom = Rig-structure ℓ .∘-is-hom
CRig-structure ℓ .id-hom-unique p _ = Equiv.injective
  (isoₜ→equiv crig-on-iso) $ Σ-pathP (p .pres-0) $
    Σ-pathP (p .pres-1) $ Σ-pathP (ext (p .pres-+)) $
      Σ-prop-pathP hlevel! (ext (p .pres-·))

CRigs : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
CRigs ℓ = Structured-objects (CRig-structure ℓ)

private variable ℓ : Level

instance
  CRigs-equational : is-equational (Rig-structure ℓ)
  CRigs-equational .invert-id-hom p .pres-0 = sym (p .pres-0)
  CRigs-equational .invert-id-hom p .pres-1 = sym (p .pres-1)
  CRigs-equational .invert-id-hom p .pres-+ _ _ = sym (p .pres-+ _ _)
  CRigs-equational .invert-id-hom p .pres-· _ _ = sym (p .pres-· _ _)

Forget : Functor (CRigs ℓ) (Sets ℓ)
Forget = Forget-structure (CRig-structure _)

Forget-comm : Functor (CRigs ℓ) (Rigs ℓ)
Forget-comm .Functor.F₀ = second comm-rig→rig
Forget-comm .Functor.F₁ f .hom x = f # x
Forget-comm .Functor.F₁ f .preserves = f .preserves
Forget-comm .Functor.F-id = refl
Forget-comm .Functor.F-∘ _ _ = refl

forget-comm-is-faithful : is-faithful (Forget-comm {ℓ})
forget-comm-is-faithful p i .hom = p i .hom
forget-comm-is-faithful p i .preserves = p i .preserves
