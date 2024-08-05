{-# OPTIONS --safe #-}
module Order.Constructions.Lower where

open import Categories.Prelude
open import Order.Base
open import Order.Constructions.Pointwise
open import Order.Constructions.Product
open import Order.Constructions.Props
import Order.Reasoning

private variable o ℓ ℓ′ : Level

module _ (P : Poset o ℓ) (ℓ′) where
  open Order.Reasoning P

  @0 Lower-sets : Poset (o ⊔ ℓ ⊔ ℓsuc ℓ′) (o ⊔ ℓ′)
  Lower-sets = P ᵒᵖᵖ ⇒ Props ℓ′

  @0 Lower-set : Type (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  Lower-set = ⌞ Lower-sets ⌟

module _ {P : Poset o ℓ} where
  open Order.Reasoning P

  ↓ : ⌞ P ⌟ → Lower-set P ℓ
  ↓ x .hom y = el! (y ≤ x)
  ↓ _ .pres-≤ = _∙_

  よₚ : P ⇒ Lower-sets P ℓ
  よₚ .hom = ↓
  よₚ .pres-≤ p _ q = q ∙ p

-- TODO
