{-# OPTIONS --safe #-}
module Cat.Skeletal where

open import Cat.Prelude
import Cat.Morphism
open import Cat.Strict

is-skeletal : ∀ {o ℓ} → Precategory o ℓ → Type (o ⊔ ℓ)
is-skeletal C =
  is-identity-system (λ (x y : Ob) → ∥ x ≅ y ∥₁) (λ _ → ∣ refl ∣₁)
    where open Cat.Morphism C


module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Morphism C

  path-from-has-iso→is-skeletal
    : (∀ {a b} → ∥ a ≅ b ∥₁ → a ＝ b)
    → is-skeletal C
  path-from-has-iso→is-skeletal = set-identity-system!

  is-skeletal→is-strict : is-skeletal C → is-strict C
  is-skeletal→is-strict skel = identity-system→is-of-hlevel! 1 skel
