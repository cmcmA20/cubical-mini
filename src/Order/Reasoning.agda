{-# OPTIONS --safe #-}
open import Order.Base

module Order.Reasoning {ℓ ℓ′} (P : Poset ℓ ℓ′) where

open import Categories.Prelude

open Poset P public

private variable a b c d : ⌞ P ⌟

infixr 2 _=⟨_⟩_ _=˘⟨_⟩_ _≤⟨_⟩_
infix  3 _≤∎

_≤⟨_⟩_ : (a : ⌞ P ⌟) → a ≤ b → b ≤ c → a ≤ c
f ≤⟨ p ⟩ q = ≤-trans p q

_=⟨_⟩_ : (a : ⌞ P ⌟) → a ＝ b → b ≤ c → a ≤ c
f =⟨ p ⟩ q = subst (_≤ _) (sym p) q

_=˘⟨_⟩_ : (a : ⌞ P ⌟) → b ＝ a → b ≤ c → a ≤ c
f =˘⟨ p ⟩ q = subst (_≤ _) p q

_≤∎ : (a : ⌞ P ⌟) → a ≤ a
f ≤∎ = ≤-refl

path→≤ : ∀ {x y} → x ＝ y → x ≤ y
path→≤ p = subst (_≤ _) (sym p) ≤-refl

path→≥ : ∀ {x y} → x ＝ y → y ≤ x
path→≥ p = subst (_≤ _) p ≤-refl
