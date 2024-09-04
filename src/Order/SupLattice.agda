{-# OPTIONS --safe #-}
module Order.SupLattice where

open import Categories.Prelude

open import Order.Base
open import Order.Diagram.Join
open import Order.Diagram.Lub
open import Order.Semilattice.Join
import Order.Diagram.Lub.Reasoning as Lubs
import Order.Reasoning

open import Combinatorics.Power

open import Data.Bool as Bool

open import Functions.Surjection

private variable ℓᵢ ℓⱼ o ℓ o′ ℓ′ o″ ℓ″ : Level

record is-sup-lattice {o ℓ} (P : Poset o ℓ) (ℓᵢ : Level) : 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓᵢ) where
  no-eta-equality
  field
    has-lubs : Has-lubs-of-size P ℓᵢ

  open Lubs P has-lubs public

  has-join-semilattice : is-join-semilattice P
  has-join-semilattice .is-join-semilattice.has-bottom = Bottom-Poset-Lub
  has-join-semilattice .is-join-semilattice.has-joins = Join-Poset-Lub

unquoteDecl H-Level-is-sup-lat =
  declare-record-hlevel 1 H-Level-is-sup-lat (quote is-sup-lattice)

record
  is-sup-lat-hom
    {P : Poset o ℓ} {Q : Poset o′ ℓ′} (f : P ⇒ Q)
    (S : is-sup-lattice P ℓᵢ) (T : is-sup-lattice Q ℓᵢ) : Type (o ⊔ ℓ′ ⊔ ℓsuc ℓᵢ)
  where
  no-eta-equality
  private
    module P = Poset P
    module Q = Order.Reasoning Q
    module Pₗ = is-sup-lattice S
    module Qₗ = is-sup-lattice T
  field
    pres-⋃ : {I : 𝒰 ℓᵢ} (F : I → P.Ob) → f # Pₗ.⋃ F Q.≤ Qₗ.⋃ (F ∙ f #_)

  has-join-slat-hom : is-join-slat-hom f Pₗ.has-join-semilattice Qₗ.has-join-semilattice
  has-join-slat-hom .is-join-slat-hom.⊥-≤ =
    f # ⊥   ~⟨ pres-⋃ (λ ()) ⟩
    Qₗ.⋃ _  =⟨ ap Qₗ.⋃ (fun-ext λ()) ⟩
    ⊥       ∎
  has-join-slat-hom .is-join-slat-hom.∪-≤ x y =
    f # (x ∪ y)    ~⟨ pres-⋃ _ ⟩
    Qₗ.⋃ _         =⟨ ap Qₗ.⋃ (ext (Bool.elim refl refl)) ⟩
    f # x ∪ f # y  ∎

  open is-join-slat-hom has-join-slat-hom public

  pres-lubs
    : {I : 𝒰 ℓᵢ} {F : I → P.Ob} (lb : P.Ob)
    → is-lub P F lb → is-lub Q {I = I} (F ∙ f #_) (f # lb)
  pres-lubs lb z .is-lub.fam≤lub i = f # is-lub.fam≤lub z i
  pres-lubs {I} {F} lb z .is-lub.least lb′ h =
    f # lb           ~⟨ f # is-lub.least z _ Pₗ.⋃-inj ⟩
    f # Pₗ.⋃ F       ~⟨ pres-⋃ F ⟩
    Qₗ.⋃ (F ∙ f #_)  ~⟨ Qₗ.⋃-universal lb′ h ⟩
    lb′              ∎

unquoteDecl H-Level-is-sup-lat-hom =
  declare-record-hlevel 1 H-Level-is-sup-lat-hom (quote is-sup-lat-hom)

instance
  ⇒-sup-lat : ⇒-notation
    (Σ[ P ꞉ Poset o ℓ ] is-sup-lattice P ℓᵢ) (Σ[ Q ꞉ Poset o′ ℓ′ ] is-sup-lattice Q ℓᵢ)
    (𝒰 (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ ℓsuc ℓᵢ))
  ⇒-sup-lat ._⇒_ (P , slp) (Q , slq) = Total-hom Monotone is-sup-lat-hom slp slq

module _ {R : Poset o″ ℓ″} where
  open Order.Reasoning R
  open is-sup-lat-hom

  instance
    Refl-sup-lat-hom : Refl (is-sup-lat-hom {ℓᵢ = ℓᵢ} {P = R} refl)
    Refl-sup-lat-hom .refl .pres-⋃ _ = refl

  module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where instance
    Trans-sup-lat-hom
      : {f : P ⇒ Q} {g : Q ⇒ R}
      → Trans (is-sup-lat-hom {ℓᵢ = ℓᵢ} f) (is-sup-lat-hom g) (is-sup-lat-hom (f ∙ g))
    Trans-sup-lat-hom {f} {g} ._∙_ α β .pres-⋃ F =
      g # α .pres-⋃ F ∙ β .pres-⋃ (F ∙ f #_)

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
    T′-inclusion = T′→T ∙ m

  sup-of-small-fam-is-lub : is-lub P m (⋃ T′-inclusion)
  sup-of-small-fam-is-lub = cast-is-lub T′≃T (λ _ → refl) has-lub
