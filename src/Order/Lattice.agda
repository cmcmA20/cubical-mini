{-# OPTIONS --safe #-}
module Order.Lattice where

open import Categories.Prelude

open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
import Order.Diagram.Join.Reasoning as Joins
import Order.Diagram.Meet.Reasoning as Meets
import Order.Reasoning
open import Order.Semilattice.Join
open import Order.Semilattice.Meet

record is-lattice {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    has-join-slat : is-join-semilattice P
    has-meet-slat : is-meet-semilattice P

  open is-join-semilattice has-join-slat public
  open is-meet-semilattice has-meet-slat public

unquoteDecl H-Level-is-lat =
  declare-record-hlevel 1 H-Level-is-lat (quote is-lattice)

private variable o ℓ o′ ℓ′ o″ ℓ″ : Level

record
  is-lattice-hom
    {P : Poset o ℓ} {Q : Poset o′ ℓ′} (f : P ⇒ Q)
    (S : is-lattice P) (T : is-lattice Q) : Type (o ⊔ ℓ′)
  where
  no-eta-equality
  private
    module S = is-lattice S
    module T = is-lattice T

  field
    has-join-slat-hom : is-join-slat-hom f S.has-join-slat T.has-join-slat
    has-meet-slat-hom : is-meet-slat-hom f S.has-meet-slat T.has-meet-slat

  open is-join-slat-hom has-join-slat-hom public
  open is-meet-slat-hom has-meet-slat-hom public

unquoteDecl H-Level-is-lattice-hom =
  declare-record-hlevel 1 H-Level-is-lattice-hom (quote is-lattice-hom)

module _ {R : Poset o″ ℓ″} where
  open Order.Reasoning R
  open is-lattice-hom

  instance
    Refl-lattice-hom : Refl (is-lattice-hom {P = R} refl)
    Refl-lattice-hom .refl .has-join-slat-hom = refl
    Refl-lattice-hom .refl .has-meet-slat-hom = refl

  module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} where instance
    Trans-lattice-hom
      : {f : P ⇒ Q} {g : Q ⇒ R}
      → Trans (is-lattice-hom f) (is-lattice-hom g) (is-lattice-hom (f ∙ g))
    Trans-lattice-hom {f} {g} ._∙_ α β .has-join-slat-hom =
      α .has-join-slat-hom ∙ β .has-join-slat-hom
    Trans-lattice-hom ._∙_ α β .has-meet-slat-hom =
      α .has-meet-slat-hom ∙ β .has-meet-slat-hom


-- TODO
-- Lattices-subcat : ∀ o ℓ → Subcat (Posets o ℓ) _ _
-- Lattices-subcat o ℓ .Subcat.is-ob = is-lattice
-- Lattices-subcat o ℓ .Subcat.is-hom = is-lattice-hom
-- Lattices-subcat o ℓ .Subcat.is-hom-prop _ _ _ = hlevel 1
-- Lattices-subcat o ℓ .Subcat.is-hom-id = id-lattice-hom
-- Lattices-subcat o ℓ .Subcat.is-hom-∘ = ∘-lattice-hom

-- Lattices : ∀ o ℓ → Precategory _ _
-- Lattices o ℓ = Subcategory (Lattices-subcat o ℓ)

-- module Lattices {o} {ℓ} = Cat.Reasoning (Lattices o ℓ)

-- Lattice : ∀ o ℓ → Type _
-- Lattice o ℓ = Lattices.Ob {o} {ℓ}
