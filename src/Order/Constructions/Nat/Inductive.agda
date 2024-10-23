{-# OPTIONS --safe #-}
module Order.Constructions.Nat.Inductive where

open import Cat.Prelude
open import Order.Base
open import Order.Complemented
open import Order.Constructions.Minmax
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Strict
open import Order.Total

open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Order.Inductive

ℕᶜᵖ : ComplementedPoset 0ℓ 0ℓ
ℕᶜᵖ .ComplementedPoset.Ob = ℕ
ℕᶜᵖ .ComplementedPoset._≤_ = _≤_
ℕᶜᵖ .ComplementedPoset._<_ m n = suc m ≤ n
ℕᶜᵖ .ComplementedPoset.≤-thin = hlevel 1
ℕᶜᵖ .ComplementedPoset.≤-refl = refl
ℕᶜᵖ .ComplementedPoset.≤-trans = _∙_
ℕᶜᵖ .ComplementedPoset.≤-antisym = ≤-antisym
ℕᶜᵖ .ComplementedPoset.<-thin = hlevel 1
ℕᶜᵖ .ComplementedPoset.<-irrefl = <-irr
ℕᶜᵖ .ComplementedPoset.<-trans = <-trans
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
ℕ-total = is-decidable-total-order.has-is-total (has-dec-total-order ℕᶜᵖ)

instance
  ℕ-bottom : Bottom ℕₚ
  ℕ-bottom .Bottom.bot = 0
  ℕ-bottom .Bottom.has-bot _ = z≤

¬-ℕ-top : ¬ Top ℕₚ
¬-ℕ-top t = suc≰id ! where open Top t

module _ where
  open decminmax (has-dec-total-order ℕᶜᵖ)

  ℕ-meets : Has-meets ℕₚ
  ℕ-meets {x} {y} .Meet.glb = min x y
  ℕ-meets {x} {y} .Meet.has-meet = min-is-meet x y

  ℕ-joins : Has-joins ℕₚ
  ℕ-joins {x} {y} .Join.lub = max x y
  ℕ-joins {x} {y} .Join.has-join = max-is-join x y


ℕₛ : StrictPoset 0ℓ 0ℓ
ℕₛ = complemented→strict ℕᶜᵖ
