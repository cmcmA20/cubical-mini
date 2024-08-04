{-# OPTIONS --safe #-}
open import Categories.Prelude

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

  ↓ᴮ : Ob → 𝒰 (ℓ ⊔ ℓ′)
  ↓ᴮ x = Σ[ b ꞉ B ] (β b ≤ x)

  ↓ᴮ→base : (x : Ob) → ↓ᴮ x → B
  ↓ᴮ→base _ = fst

  ↓ᴮ-inclusion : (x : Ob) → ↓ᴮ x → Ob
  ↓ᴮ-inclusion x = β ∘ₜ ↓ᴮ→base x

  ↓ᴮ-≤ : {x y : Ob} → x ≤ y → ↓ᴮ x → ↓ᴮ y
  ↓ᴮ-≤ le = second (_∙ le)

  record is-basis : 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′) where
    no-eta-equality
    field
      ≤-is-small : (x : Ob) (b : B) → is-of-size ℓ′ (β b ≤ x)
      ↓-is-sup : (x : Ob) → is-lub P (↓ᴮ-inclusion x) x

    _≤ᴮ_ : (b : B) → (x : Ob) → 𝒰 ℓ′
    b ≤ᴮ x = ⌞ ≤-is-small x b ⌟

    ≤ᴮ≃≤ : {b : B} {x : Ob} → b ≤ᴮ x ≃ β b ≤ x
    ≤ᴮ≃≤ {b} {x} = ≤-is-small x b .snd

    ≤ᴮ→≤ : {b : B} {x : Ob} → b ≤ᴮ x → β b ≤ x
    ≤ᴮ→≤ = ≤ᴮ≃≤ $_

    ≤→≤ᴮ : {b : B} {x : Ob} → β b ≤ x → b ≤ᴮ x
    ≤→≤ᴮ = ≤ᴮ≃≤ ⁻¹ $_

    ≤ᴮ-is-prop : {b : B} {x : Ob} → is-prop (b ≤ᴮ x)
    ≤ᴮ-is-prop = ≃→is-of-hlevel! 1 ≤ᴮ≃≤

    small-↓ᴮ : Ob → 𝒰 ℓ′
    small-↓ᴮ x = Σ[ b ꞉ B ] b ≤ᴮ x

    small-↓ᴮ-inclusion : {x : Ob} → small-↓ᴮ x → Ob
    small-↓ᴮ-inclusion = β ∘ₜ fst

    small-↓ᴮ-≃-↓ᴮ : {x : Ob} → small-↓ᴮ x ≃ ↓ᴮ x
    small-↓ᴮ-≃-↓ᴮ {x} = Σ-ap-snd λ _ → ≤ᴮ≃≤

    ↓ᴮ-is-small : {x : Ob} → is-of-size ℓ′ (↓ᴮ x)
    ↓ᴮ-is-small {x} = small-↓ᴮ x , small-↓ᴮ-≃-↓ᴮ

    is-supᴮ' : {x : Ob} → x ＝ sup (small-↓ᴮ-inclusion {x})
    is-supᴮ' {x} = equiv-reindexing (small-↓ᴮ-≃-↓ᴮ .snd)
      x
      (sup small-↓ᴮ-inclusion)
      (↓-is-sup x)
      (suprema small-↓ᴮ-inclusion)

    is-supᴮ : {x : Ob} → is-lub P (small-↓ᴮ-inclusion {x}) x
    is-supᴮ {x} = subst (is-lub P (small-↓ᴮ-inclusion {x}))
                        (is-supᴮ' {x} ⁻¹)
                        (suprema small-↓ᴮ-inclusion)

    is-ubᴮ : {x : Ob}
           → (s : small-↓ᴮ x) → small-↓ᴮ-inclusion s ≤ x
    is-ubᴮ = fam≤lub is-supᴮ

    is-lubᴮ : {x : Ob} (u' : Ob)
            → ((s : small-↓ᴮ x) → small-↓ᴮ-inclusion s ≤ u') → x ≤ u'
    is-lubᴮ = least is-supᴮ

    instance
      H-Level-≤ᴮ : ∀{n} {b : B} {x : Ob} ⦃ _ : 1 ≤ʰ n ⦄ → H-Level n (b ≤ᴮ x)
      H-Level-≤ᴮ ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance ≤ᴮ-is-prop
