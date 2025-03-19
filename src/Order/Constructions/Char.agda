{-# OPTIONS --safe #-}
module Order.Constructions.Char where

open import Cat.Prelude
open import Order.Base
open import Order.Complemented
open import Order.Constructions.Minmax
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Strict
open import Order.Total

open import Data.Char.Base
open import Data.Char.Path
open import Data.Char.Properties
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Order.Base renaming (_<_ to _<ℕ_ ; <-trans to <ℕ-trans ; _≤_ to _≤ℕ_)
open import Data.Nat.Order.Base
  using ( H-Level-≤ ; H-Level-<; Refl-≤ ; Trans-≤ ; Reflects-suc≰id ; Reflects-suc≰z)
  public

-- TODO a construction for defining posets via injective functions
Charᶜᵖ : ComplementedPoset 0ℓ 0ℓ
Charᶜᵖ .ComplementedPoset.Ob = Char
Charᶜᵖ .ComplementedPoset._≤_ x y = char→ℕ x ≤ℕ char→ℕ y
Charᶜᵖ .ComplementedPoset._<_ x y = char→ℕ x <ℕ char→ℕ y
Charᶜᵖ .ComplementedPoset.≤-thin = hlevel 1
Charᶜᵖ .ComplementedPoset.≤-refl = refl
Charᶜᵖ .ComplementedPoset.≤-trans = _∙_
Charᶜᵖ .ComplementedPoset.≤-antisym x≤y y≤x = char→ℕ-inj $ ≤-antisym x≤y y≤x
Charᶜᵖ .ComplementedPoset.<-thin = hlevel 1
Charᶜᵖ .ComplementedPoset.<-irrefl = <-irr
Charᶜᵖ .ComplementedPoset.<-trans = <ℕ-trans
Charᶜᵖ .ComplementedPoset.≤≃≯ = ≤≃≯
Charᶜᵖ .ComplementedPoset.<≃≱ = <≃≱

open ComplementedPoset

Charₚ : Poset 0ℓ 0ℓ
Charₚ = complemented→poset Charᶜᵖ

Char-dec-total : is-decidable-total-order Charₚ
Char-dec-total = has-dec-total-order Charᶜᵖ

Char-total : is-total-order Charₚ
Char-total = is-decidable-total-order.has-is-total Char-dec-total

module _ where
  open decminmax Char-dec-total

  Char-meets : Has-meets Charₚ
  Char-meets = min-meets

  Char-joins : Has-joins Charₚ
  Char-joins = max-joins

Charₛ : StrictPoset 0ℓ 0ℓ
Charₛ = complemented→strict Charᶜᵖ

Char-dec-strict-total : is-decidable-strict-total-order Charₛ
Char-dec-strict-total = has-dec-strict-total-order Charᶜᵖ
