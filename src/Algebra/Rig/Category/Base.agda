{-# OPTIONS --safe #-}
module Algebra.Rig.Category.Base where

open import Algebra.Rig
open import Algebra.Semiring.Category using (Semiring-structure; Semirings)

open import Categories.Displayed.Univalence.Thin
open import Categories.Prelude

open Semiring-hom
open Rig-on

Rig-structure : ∀ ℓ → Thin-structure ℓ Rig-on
Rig-structure ℓ = Full-substructure ℓ Rig-on Semiring-on
  (λ _ → rig-on↪semiring-on) (Semiring-structure ℓ)

Rigs : ∀ ℓ → Precategory (ℓsuc ℓ) ℓ
Rigs ℓ = Structured-objects (Rig-structure ℓ)

Rig : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Rig ℓ = Precategory.Ob (Rigs ℓ)

private variable ℓ : Level

instance
  Rigs-equational : is-equational (Rig-structure ℓ)
  Rigs-equational .invert-id-hom p .pres-0 = sym (p .pres-0)
  Rigs-equational .invert-id-hom p .pres-1 = sym (p .pres-1)
  Rigs-equational .invert-id-hom p .pres-+ _ _ = sym (p .pres-+ _ _)
  Rigs-equational .invert-id-hom p .pres-· _ _ = sym (p .pres-· _ _)

Forget : Functor (Rigs ℓ) (Sets ℓ)
Forget = Forget-structure (Rig-structure _)

Forget-absorb : Functor (Rigs ℓ) (Semirings ℓ)
Forget-absorb .Functor.F₀ = second (rig-on↪semiring-on #_)
Forget-absorb .Functor.F₁ f .hom x = f # x
Forget-absorb .Functor.F₁ f .preserves = f .preserves
Forget-absorb .Functor.F-id = refl
Forget-absorb .Functor.F-∘ _ _ = refl

forget-absorb-is-faithful : is-faithful (Forget-absorb {ℓ})
forget-absorb-is-faithful p i .hom = p i .hom
forget-absorb-is-faithful p i .preserves = p i .preserves
