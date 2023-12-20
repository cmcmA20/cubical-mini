{-# OPTIONS --safe #-}
module Order.Total where

open import Categories.Prelude

open import Order.Base

private variable o ℓ : Level

is-toset : Poset o ℓ → 𝒰 _
is-toset P = ∀ {x y} → x ≤ y ⊎₁ y ≤ x where open Poset P
