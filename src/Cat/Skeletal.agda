{-# OPTIONS --safe #-}
module Cat.Skeletal where

open import Cat.Prelude
import Cat.Morphism
open import Cat.Strict

module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Morphism C

  is-skeletal : Type (o ⊔ ℓ)
  is-skeletal = is-identity-system (λ (x y : Ob) → ∥ x ≅ y ∥₁) (λ _ → ∣ refl ∣₁)

  path-from-has-iso→is-skeletal
    : (∀ {a b : Ob} → ∥ a ≅ b ∥₁ → a ＝ b)
    → is-skeletal
  path-from-has-iso→is-skeletal = set-identity-system!

  is-skeletal→is-strict : is-skeletal → is-strict C
  is-skeletal→is-strict skel = identity-system→is-of-hlevel! 1 skel
