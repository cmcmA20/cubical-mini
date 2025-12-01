{-# OPTIONS --safe #-}
module Order.SupLattice.SmallPresentation where

open import Cat.Prelude

open import Order.Base
open import Order.SupLattice
open import Order.SupLattice.SmallBasis

open import Combinatorics.Power

record small-presentation
  {o ℓ ℓ′} {P : Poset o ℓ} {L : is-sup-lattice P ℓ′}
  {B : 𝒰 ℓ′} {β : B → ⌞ P ⌟} (h : is-basis L β) : 𝒰 (ℓsuc ℓ′) where
    no-eta-equality
    open is-basis h
    field
      J : 𝒰 ℓ′
      Y : J → ℙ B ℓ′
      R : ℙ (B × ℙ B ℓ′) ℓ′
      has-small
        : (b : B) (X : ℙ B ℓ′)
        → b ≤ᴮ ℙ⋃ L β X
        ≃ ∃[ j ꞉ J ] Y j ⊆ X × ((b , Y j) ∈ R)
