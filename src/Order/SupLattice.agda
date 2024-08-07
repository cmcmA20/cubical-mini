{-# OPTIONS --safe #-}
module Order.SupLattice where

open import Categories.Prelude

open import Order.Base
open import Order.Diagram.Lub
import Order.Diagram.Lub.Reasoning
import Order.Reasoning

open import Combinatorics.Power

open import Functions.Surjection

private variable ℓᵢ ℓⱼ o ℓ o′ ℓ′ o″ ℓ″ : Level

record is-sup-lattice {o ℓ} (P : Poset o ℓ) (ℓᵢ : Level) : 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓᵢ) where
  no-eta-equality
  field has-lubs : Has-lubs-of-size P ℓᵢ
  open Order.Diagram.Lub.Reasoning P has-lubs public

unquoteDecl H-Level-is-sup-lat =
  declare-record-hlevel 1 H-Level-is-sup-lat (quote is-sup-lattice)

record
  is-sup-lat-hom
    {P : Poset o ℓ} {Q : Poset o′ ℓ′} (f : P ⇒ Q)
    (S : is-sup-lattice P ℓᵢ) (T : is-sup-lattice Q ℓᵢ) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ ℓsuc ℓᵢ)
  where
  no-eta-equality
  private module P = Poset P
  field
    pres-lubs
      : {I : 𝒰 ℓᵢ} {F : I → P.Ob} (lb : P.Ob)
      → is-lub P F lb → is-lub Q {I = I} (λ j → f # F j) (f # lb)

unquoteDecl H-Level-is-sup-lat-hom =
  declare-record-hlevel 1 H-Level-is-sup-lat-hom (quote is-sup-lat-hom)

module _ {R : Poset o″ ℓ″} where
  open Order.Reasoning R
  open is-sup-lat-hom

  instance
    Refl-sup-lat-hom : Refl (is-sup-lat-hom {ℓᵢ = ℓᵢ} {P = R} refl)
    Refl-sup-lat-hom .refl .pres-lubs _ = refl

  module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where instance
    Trans-sup-lat-hom
      : {f : P ⇒ Q} {g : Q ⇒ R}
      → Trans (is-sup-lat-hom {ℓᵢ = ℓᵢ} f) (is-sup-lat-hom g) (is-sup-lat-hom (f ∙ g))
    Trans-sup-lat-hom {f} ._∙_ α β .pres-lubs x y = β .pres-lubs (f # x) (α .pres-lubs x y)

module _
  {o ℓ ℓ′ : Level}
  {P : Poset o ℓ} (L : is-sup-lattice P ℓ′)
  {T : 𝒰 ℓ′} (m : T → ⌞ P ⌟) where
  open Order.Reasoning P
  open is-sup-lattice L

  joins-preserve-containment : (A B : ℙ T ℓ′)
                             → A ⊆ B
                             → ⋃ (ℙ→fam m A .snd) ≤ ⋃ (ℙ→fam m B .snd)
  joins-preserve-containment _ _ A⊆B = ⋃≤⋃-over (second A⊆B) λ _ → refl

module _
  {o ℓ ℓ′ : Level}
  {P : Poset o ℓ} (L : is-sup-lattice P ℓ′)
  {I : 𝒰 ℓᵢ} (m : I → ⌞ P ⌟)
  (I-small : is-of-size ℓ′ I) where
  open Order.Reasoning P
  open is-sup-lattice L
  open is-lub

  private
    T′≃T : ⌞ I-small ⌟ ≃ I
    T′≃T = resizing-cond I-small

    T′→T : ⌞ I-small ⌟ → I
    T′→T = T′≃T $_

    T′-inclusion : ⌞ I-small ⌟ → Ob
    T′-inclusion = m ∘ₜ T′→T

  sup-of-small-fam-is-lub : is-lub P m (⋃ T′-inclusion)
  sup-of-small-fam-is-lub = cast-is-lub T′≃T (λ _ → refl) has-lub
