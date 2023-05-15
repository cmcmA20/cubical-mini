{-# OPTIONS --safe #-}
module Structures.Constant where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Univalence.SIP

private variable
  ℓ ℓ₁ : Level
  A : Type ℓ

Constant-str : (A : Type ℓ) → Structure {ℓ₁} ℓ (const A)
Constant-str T .is-hom (A , x) (B , y) f = x ＝ y

Constant-str-is-univalent : is-univalent (Constant-str {ℓ₁ = ℓ₁} A)
Constant-str-is-univalent f = idₑ

Constant-action : (A : Type ℓ) → Equiv-action {ℓ = ℓ₁} (λ X → A)
Constant-action A eqv = idₑ

Constant-action-is-transport
  : is-transport-str {ℓ = ℓ₁} (Constant-action A)
Constant-action-is-transport f s = sym (transport-refl _)
