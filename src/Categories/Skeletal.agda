{-# OPTIONS --safe #-}
module Categories.Skeletal where

open import Categories.Prelude
import Categories.Morphism
open import Categories.Strict

is-skeletal : ∀ {o ℓ} → Precategory o ℓ → Type (o ⊔ ℓ)
is-skeletal C =
  is-identity-system (λ x y → ∥ Isomorphism x y ∥₁) (λ _ → ∣ id-iso ∣₁)
    where open Categories.Morphism C


module _ {o ℓ} (C : Precategory o ℓ) where
  open Categories.Morphism C

  path-from-has-iso→is-skeletal
    : (∀ {a b} → ∥ Isomorphism a b ∥₁ → a ＝ b)
    → is-skeletal C
  path-from-has-iso→is-skeletal = set-identity-system hlevel!

  is-skeletal→is-strict : is-skeletal C → is-strict C
  is-skeletal→is-strict skel = identity-system→is-of-hlevel 1 skel hlevel!
