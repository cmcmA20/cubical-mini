{-# OPTIONS --safe #-}
module Order.SupLattice where

open import Categories.Prelude

open import Functions.Surjection
open import Combinatorics.Power

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
import Order.Reasoning

private variable o ℓ ℓ′ : Level

record is-sup-lattice (P : Poset o ℓ) (ℓ′ : Level) : 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′) where
  no-eta-equality
  open Poset P
  field
    sup     : {I : 𝒰 ℓ′} (F : I → Ob) → Ob
    suprema : {I : 𝒰 ℓ′} (F : I → Ob) → is-lub P F (sup F)


module _ {o ℓ ℓ′ : Level}
         {P : Poset o ℓ}
         (L : is-sup-lattice P ℓ′)
         {T : 𝒰 ℓ′}
         (m : T → ⌞ P ⌟)
       where

  open Poset P
  open is-lub
  open is-sup-lattice L

  joins-preserve-containment : (P Q : ℙ T ℓ′)
                             → P ⊆ Q
                             → sup (ℙ→fam m P .snd) ≤ sup (ℙ→fam m Q .snd)
  joins-preserve-containment P Q C =
    suprema (ℙ→fam m P .snd) .least (sup (ℙ→fam m Q .snd)) $
    suprema (ℙ→fam m Q .snd) .fam≤lub ∘ₜ second C

module _ {o ℓ ℓ′ ℓ″ : Level}
         {P : Poset o ℓ}
         (L : is-sup-lattice P ℓ′)
         {T : 𝒰 ℓ″}
         (m : T → ⌞ P ⌟)
         (T-sz : is-of-size ℓ′ T)
       where

  open Poset P
  open is-lub
  open is-sup-lattice L

  private
    T′ : 𝒰 ℓ′
    T′ = ⌞ T-sz ⌟

    T′≃T : T′ ≃ T
    T′≃T = resizing-cond T-sz

    T′→T : T′ → T
    T′→T = T′≃T $_

    T′-inclusion : T′ → Ob
    T′-inclusion = m ∘ₜ T′→T

  sup-of-small-fam-is-lub : is-lub P m (sup T′-inclusion)
  sup-of-small-fam-is-lub .fam≤lub t = subst (λ q → m q ≤ sup T′-inclusion)
                                             (is-equiv→unit ((T′≃T ⁻¹) .snd) t)
                                             (suprema T′-inclusion .fam≤lub (T′≃T ⁻¹ $ t))
  sup-of-small-fam-is-lub .least u′ ub = suprema T′-inclusion .least u′ (ub ∘ₜ T′→T)
