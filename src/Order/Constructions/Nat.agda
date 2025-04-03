{-# OPTIONS --safe #-}
-- TODO generalize to naturally ordered monoid/semiring
module Order.Constructions.Nat where

open import Cat.Prelude
open import Order.Base
open import Order.Complemented
open import Order.Constructions.Minmax
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Semilattice.Join
open import Order.Strict
open import Order.Total
open import Order.Ordinal

open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Order.Base renaming (_<_ to _<ℕ_ ; <-trans to <ℕ-trans ; _≤_ to _≤ℕ_)
open import Data.Nat.Order.Base
  using ( H-Level-≤ ; H-Level-<; Refl-≤ ; Trans-≤ ; Reflects-suc≰id ; Reflects-suc≰z)
  public

ℕᶜᵖ : ComplementedPoset 0ℓ 0ℓ
ℕᶜᵖ .ComplementedPoset.Ob = ℕ
ℕᶜᵖ .ComplementedPoset._≤_ = _≤ℕ_
ℕᶜᵖ .ComplementedPoset._<_ = _<ℕ_
ℕᶜᵖ .ComplementedPoset.≤-thin = hlevel 1
ℕᶜᵖ .ComplementedPoset.≤-refl = refl
ℕᶜᵖ .ComplementedPoset.≤-trans = _∙_
ℕᶜᵖ .ComplementedPoset.≤-antisym = ≤-antisym
ℕᶜᵖ .ComplementedPoset.<-thin = hlevel 1
ℕᶜᵖ .ComplementedPoset.<-irrefl = <-irr
ℕᶜᵖ .ComplementedPoset.<-trans = <ℕ-trans
ℕᶜᵖ .ComplementedPoset.≤≃≯ = ≤≃≯
ℕᶜᵖ .ComplementedPoset.<≃≱ = <≃≱

open ComplementedPoset

ℕₚ : Poset 0ℓ 0ℓ
ℕₚ = complemented→poset ℕᶜᵖ

Suc : ℕₚ ⇒ ℕₚ
Suc .hom    = suc
Suc .pres-≤ = s≤s

ℕ-dec-total : is-decidable-total-order ℕₚ
ℕ-dec-total = has-dec-total-order ℕᶜᵖ

ℕ-total : is-total-order ℕₚ
ℕ-total = is-decidable-total-order.has-is-total ℕ-dec-total

instance
  ℕ-bottom : Bottom ℕₚ
  ℕ-bottom .Bottom.bot = 0
  ℕ-bottom .Bottom.has-bot _ = z≤

¬-ℕ-top : ¬ Top ℕₚ
¬-ℕ-top t = suc≰id ! where open Top t

module _ where
  open decminmax ℕ-dec-total

  ℕ-meets : Has-meets ℕₚ
  ℕ-meets = min-meets

  ℕ-joins : Has-joins ℕₚ
  ℕ-joins = max-joins

  ℕ-join-slat : is-join-semilattice ℕₚ
  ℕ-join-slat .is-join-semilattice.has-bottom = ℕ-bottom
  ℕ-join-slat .is-join-semilattice.has-joins  = ℕ-joins

ℕₛ : StrictPoset 0ℓ 0ℓ
ℕₛ = complemented→strict ℕᶜᵖ

ℕw : WESet 0ℓ 0ℓ
ℕw .WESet.Ob = ℕ
ℕw .WESet._<_ = _<ℕ_
ℕw .WESet.<-thin = hlevel 1
ℕw .WESet.<-wf = <-is-wf
ℕw .WESet.<-lext = <-lext

ℕω : Ordinal 0ℓ
ℕω = ℕw , <ℕ-trans
