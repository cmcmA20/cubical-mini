{-# OPTIONS --safe #-}
open import Categories.Prelude
open import Meta.Prelude
open import Foundations.Equiv.Size

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
open import Order.SupLattice

import Order.Reasoning

module Order.SupLattice.SmallBasis {o ℓ ℓ′} {B : 𝒰 ℓ′}
                                   (P : Poset o ℓ)
                                   (L : is-sup-lattice P ℓ′)
                                   (β : B → ⌞ P ⌟)
                                 where

  open Poset P
  open is-lub
  open is-sup-lattice L

  ↓ᴮ : ⌞ P ⌟ → 𝒰 (ℓ ⊔ ℓ′)
  ↓ᴮ x = Σ[ b ꞉ B ] (β b ≤ x)

  ↓ᴮ→base : (x : ⌞ P ⌟) → ↓ᴮ x → B
  ↓ᴮ→base x = fst

  ↓ᴮ-inclusion : (x : ⌞ P ⌟) → ↓ᴮ x → ⌞ P ⌟
  ↓ᴮ-inclusion x = β ∘ ↓ᴮ→base x

  record is-basis : 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′) where
    no-eta-equality

    field
      ≤-is-small : (x : ⌞ P ⌟) (b : B) → is-of-size ℓ′ (β b ≤ x)
      ↓-is-sup : (x : ⌞ P ⌟) → is-lub P (↓ᴮ-inclusion x) x

    _≤ᴮ_ : (b : B) → (x : ⌞ P ⌟) → 𝒰 ℓ′
    b ≤ᴮ x = ⌞ ≤-is-small x b ⌟

    ≤ᴮ≃≤ : {b : B} {x : ⌞ P ⌟} → b ≤ᴮ x ≃ β b ≤ x
    ≤ᴮ≃≤ {b} {x} = ≤-is-small x b .snd

    ≤ᴮ→≤ : {b : B} {x : ⌞ P ⌟} → b ≤ᴮ x → β b ≤ x
    ≤ᴮ→≤ = ≤ᴮ≃≤ $_

    ≤→≤ᴮ : {b : B} {x : ⌞ P ⌟} → β b ≤ x → b ≤ᴮ x
    ≤→≤ᴮ = ≤ᴮ≃≤ ⁻¹ $_

    ≤ᴮ-is-prop : {b : B} {x : ⌞ P ⌟} → is-prop (b ≤ᴮ x)
    ≤ᴮ-is-prop {b} {x} = ≃→is-of-hlevel 1 ≤ᴮ≃≤ ≤-thin

    small-↓ᴮ : ⌞ P ⌟ → 𝒰 ℓ′
    small-↓ᴮ x = Σ[ b ꞉ B ] b ≤ᴮ x

    small-↓ᴮ-inclusion : {x : ⌞ P ⌟} → small-↓ᴮ x → ⌞ P ⌟
    small-↓ᴮ-inclusion = β ∘ fst

    small-↓ᴮ-≃-↓ᴮ : {x : ⌞ P ⌟} → small-↓ᴮ x ≃ ↓ᴮ x
    small-↓ᴮ-≃-↓ᴮ {x} = Σ-ap-snd λ _ → ≤ᴮ≃≤

    ↓ᴮ-is-small : {x : ⌞ P ⌟} → is-of-size ℓ′ (↓ᴮ x)
    ↓ᴮ-is-small {x} = small-↓ᴮ x , small-↓ᴮ-≃-↓ᴮ

    is-supᴮ' : {x : ⌞ P ⌟} → x ＝ sup (small-↓ᴮ-inclusion {x})
    is-supᴮ' {x} =
      reindexing-along-equiv-=-sup {P = P}
        small-↓ᴮ-≃-↓ᴮ (↓ᴮ-inclusion x) x (sup small-↓ᴮ-inclusion)
        (↓-is-sup x) (suprema small-↓ᴮ-inclusion)

    is-supᴮ : {x : ⌞ P ⌟} → is-lub P (small-↓ᴮ-inclusion {x}) x
    is-supᴮ {x} = subst (is-lub P (small-↓ᴮ-inclusion {x}))
                        (is-supᴮ' {x} ⁻¹)
                        (suprema small-↓ᴮ-inclusion)

    is-ubᴮ : {x : ⌞ P ⌟}
           → (s : small-↓ᴮ x) → small-↓ᴮ-inclusion s ≤ x
    is-ubᴮ = fam≤lub is-supᴮ

    is-lubᴮ : {x : ⌞ P ⌟}
            → (u' : Ob) → ((s : small-↓ᴮ x) → small-↓ᴮ-inclusion s ≤ u') → x ≤ u'
    is-lubᴮ = least is-supᴮ
