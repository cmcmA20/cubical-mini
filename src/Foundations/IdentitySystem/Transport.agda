{-# OPTIONS --safe #-}
module Foundations.IdentitySystem.Transport where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Univalence
open import Foundations.IdentitySystem.Base

record
  is-transport-system {ℓ ℓ′ ℓ″}
    {A : Type ℓ} {B : A → Type ℓ′}
    {R : A → A → Type ℓ″} {rfl : ∀ a → R a a}
    (ids : Erased (is-identity-system R rfl))
    : 𝒰 (ℓ ⊔ ℓ′ ⊔ ℓ″)
  where
    field
      subst     : {x y : A} (p : R x y) → B x → B y
      subst-coh : {x y : A} (p : R x y) (b : B x)
                → Erased (subst p b ＝ substₚ B (ids .erased. to-path p) b)

    -- subst⁻-subst : {x y : A} (p : R x y) (b : B x) → subst {!p ⁻¹!} (subst p b) ＝ b
    -- subst⁻-subst p b = {!!}

open is-transport-system ⦃ ... ⦄ public
  using (subst)

instance
  path-transport-system
    : ∀{ℓ ℓ′} {A : 𝒰 ℓ} {B : A → 𝒰 ℓ′}
    → is-transport-system {B = B} (erase path-identity-system)
  path-transport-system .is-transport-system.subst = substₚ _
  path-transport-system .is-transport-system.subst-coh _ _ .erased = refl
  {-# INCOHERENT path-transport-system #-}

  univalence-transport-system
    : ∀{ℓ} → is-transport-system {ℓ′ = ℓ} {B = id} (erase univalence-identity-system)
  univalence-transport-system .is-transport-system.subst = fst
  univalence-transport-system .is-transport-system.subst-coh e b .erased = ua-β e b ⁻¹
  {-# OVERLAPPABLE univalence-transport-system #-}
