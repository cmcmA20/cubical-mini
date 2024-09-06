{-# OPTIONS --safe #-}
open import Order.Base

module Order.Reasoning {ℓ ℓ′} (P : Poset ℓ ℓ′) where

open import Cat.Prelude

open Poset P public

private variable a b c d : ⌞ P ⌟

infixr 2 _≤⟨_⟩_
_≤⟨_⟩_ : (a : ⌞ P ⌟) → a ≤ b → b ≤ c → a ≤ c
f ≤⟨ p ⟩ q = p ∙ q

=→≤ : ∀ {x y} → x ＝ y → x ≤ y
=→≤ = =→~

=→≥ : ∀ {x y} → x ＝ y → y ≤ x
=→≥ = =→~⁻
