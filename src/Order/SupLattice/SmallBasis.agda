{-# OPTIONS --safe #-}
open import Cat.Prelude

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
open import Order.SupLattice

import Order.Reasoning

module Order.SupLattice.SmallBasis
  {o ℓ ℓ′}
  {P : Poset o ℓ} (L : is-sup-lattice P ℓ′)
  {B : 𝒰 ℓ′} (β : B → ⌞ P ⌟) where

  open Order.Reasoning P
  open is-sup-lattice L
  open is-lub

  ↓ᴮ : Ob → 𝒰 (ℓ ⊔ ℓ′)
  ↓ᴮ x = Σ[ b ꞉ B ] (β b ≤ x)

  ↓ᴮ-inclusion : (x : Ob) → ↓ᴮ x → Ob
  ↓ᴮ-inclusion x = β ∘ₜ fst

  ↓ᴮ-≤ : {x y : Ob} → x ≤ y → ↓ᴮ x → ↓ᴮ y
  ↓ᴮ-≤ le = second (_∙ le)

  record is-basis : 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′) where
    no-eta-equality
    field
      ≤-is-small : (x : Ob) (b : B) → is-of-size ℓ′ (β b ≤ x)
      -- technically we only need the least part of is-lub, as fam≤lub holds by definition of ↓ᴮ
      ↓-is-sup   : (x : Ob) → is-lub P (↓ᴮ-inclusion x) x

    _≤ᴮ_ : (b : B) → (x : Ob) → 𝒰 ℓ′
    b ≤ᴮ x = ⌞ ≤-is-small x b ⌟

    ≤ᴮ≃≤ : {b : B} {x : Ob} → b ≤ᴮ x ≃ β b ≤ x
    ≤ᴮ≃≤ {b} {x} = resizing-cond (≤-is-small x b)

    ≤ᴮ→≤ : {b : B} {x : Ob} → b ≤ᴮ x → β b ≤ x
    ≤ᴮ→≤ = ≤ᴮ≃≤ $_

    ≤→≤ᴮ : {b : B} {x : Ob} → β b ≤ x → b ≤ᴮ x
    ≤→≤ᴮ = ≤ᴮ≃≤ ⁻¹ $_

    ≤ᴮ-is-prop : {b : B} {x : Ob} → is-prop (b ≤ᴮ x)
    ≤ᴮ-is-prop = ≃→is-of-hlevel! 1 ≤ᴮ≃≤

    instance
      H-Level-≤ᴮ : ∀{n} {b : B} {x : Ob} ⦃ _ : 1 ≤ʰ n ⦄ → H-Level n (b ≤ᴮ x)
      H-Level-≤ᴮ ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance ≤ᴮ-is-prop

    small-↓ᴮ : Ob → 𝒰 ℓ′
    small-↓ᴮ x = Σ[ b ꞉ B ] b ≤ᴮ x

    small-↓ᴮ-inclusion : {x : Ob} → small-↓ᴮ x → Ob
    small-↓ᴮ-inclusion = β ∘ₜ fst

    small-↓ᴮ-≃-↓ᴮ : {x : Ob} → small-↓ᴮ x ≃ ↓ᴮ x
    small-↓ᴮ-≃-↓ᴮ {x} = Σ-ap-snd λ _ → ≤ᴮ≃≤

    ↓ᴮ-is-small : {x : Ob} → is-of-size ℓ′ (↓ᴮ x)
    ↓ᴮ-is-small {x} = small-↓ᴮ x , small-↓ᴮ-≃-↓ᴮ

    -- this is the only part that suplattice is required for
    is-supᴮ' : {x : Ob} → x ＝ ⋃ (small-↓ᴮ-inclusion {x})
    is-supᴮ' {x} = equiv-reindexing (small-↓ᴮ-≃-↓ᴮ)
      x
      (⋃ small-↓ᴮ-inclusion)
      (↓-is-sup x)
      has-lub

    is-supᴮ : {x : Ob} → is-lub P (small-↓ᴮ-inclusion {x}) x
    is-supᴮ {x} = subst (is-lub P (small-↓ᴮ-inclusion {x}))
                        (is-supᴮ' {x} ⁻¹)
                        has-lub

    is-ubᴮ : {x : Ob}
           → (s : small-↓ᴮ x) → small-↓ᴮ-inclusion s ≤ x
    is-ubᴮ = fam≤lub is-supᴮ

    is-lubᴮ : {x : Ob} (u' : Ob)
            → ((s : small-↓ᴮ x) → small-↓ᴮ-inclusion s ≤ u') → x ≤ u'
    is-lubᴮ = least is-supᴮ

  unquoteDecl is-basis-Iso = declare-record-iso is-basis-Iso (quote is-basis)

  -- TODO requires is-of-size-is-prop
  -- @0 is-basis-is-prop : is-prop is-basis
  -- is-basis-is-prop = ≅→is-of-hlevel 1 is-basis-Iso (×-is-of-hlevel 1 {!!} hlevel!)

  ≤-from-≤ᴮ : is-basis
           → {x y : Ob}
           → ((b : B) → β b ≤ x → β b ≤ y)
           → x ≤ y
  ≤-from-≤ᴮ bas {x} {y} h = is-basis.↓-is-sup bas x .least y λ i → h (fst i) (snd i)
