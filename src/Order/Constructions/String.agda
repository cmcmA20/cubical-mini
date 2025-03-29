{-# OPTIONS --safe #-}
module Order.Constructions.String where

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
open import Order.Trichotomous

open import Order.Constructions.Lex
open import Order.Constructions.Char

open import Data.List.Base
open import Data.Char.Base
open import Data.Char.Path
open import Data.String.Base
open import Data.String.Path
open import Data.String.Properties

ListCharₚ : Poset 0ℓ 0ℓ
ListCharₚ = []≤ Charₛ ⦃ auto ⦄

Strₚ : Poset 0ℓ 0ℓ
Strₚ .Poset.Ob = String
Strₚ .Poset._≤_ x y =
  ListCharₚ .Order.Base.Poset._≤_ (string→list x) (string→list y)
Strₚ .Poset.≤-thin {x} {y} =
  ListCharₚ .Order.Base.Poset.≤-thin
    {x = string→list x} {y = string→list y}
Strₚ .Poset.≤-refl {x} =
  ListCharₚ .Order.Base.Poset.≤-refl
    {x = string→list x}
Strₚ .Poset.≤-trans {x} {y} {z} =
  ListCharₚ .Order.Base.Poset.≤-trans
    {x = string→list x} {y = string→list y} {z = string→list z}
Strₚ .Poset.≤-antisym {x} {y} x≤y y≤x =
  string→list-inj $
  ListCharₚ .Order.Base.Poset.≤-antisym
    {x = string→list x} {y = string→list y} x≤y y≤x

ListChar-dec-total : is-decidable-total-order ListCharₚ
ListChar-dec-total = []≤-dto Char-dec-strict-total

Str-total : is-total-order Strₚ
Str-total .is-total-order.compare x y =
  ListChar-dec-total .Order.Total.is-decidable-total-order.compare (string→list x) (string→list y)

Str-dec-total : is-decidable-total-order Strₚ
Str-dec-total .is-decidable-total-order.has-is-total = Str-total
Str-dec-total .is-decidable-total-order.dec-≤ {x} {y} =
  ListChar-dec-total .Order.Total.is-decidable-total-order.dec-≤
    {x = string→list x} {y = string→list y}
Str-dec-total .is-decidable-total-order.has-discrete = String-is-discrete

-- TODO generalize to lex
instance
  Str-bottom : Bottom Strₚ
  Str-bottom .Bottom.bot = ""
  Str-bottom .Bottom.has-bot _ = lift tt

-- TODO ?
-- ¬-Str-top : ¬ Top Strₚ

module _ where
  open decminmax Str-dec-total

  Str-meets : Has-meets Strₚ
  Str-meets = min-meets

  Str-joins : Has-joins Strₚ
  Str-joins = max-joins

  Str-join-slat : is-join-semilattice Strₚ
  Str-join-slat .is-join-semilattice.has-bottom = Str-bottom
  Str-join-slat .is-join-semilattice.has-joins  = Str-joins

-- strict

ListCharₛ : StrictPoset 0ℓ 0ℓ
ListCharₛ = []< Charₛ ⦃ auto ⦄

Strₛ : StrictPoset 0ℓ 0ℓ
Strₛ .StrictPoset.Ob = String
Strₛ .StrictPoset._<_ x y =
  ListCharₛ .Order.Strict.StrictPoset._<_ (string→list x) (string→list y)
Strₛ .StrictPoset.<-thin {x} {y} =
  ListCharₛ .Order.Strict.StrictPoset.<-thin
    {x = string→list x} {y = string→list y}
Strₛ .StrictPoset.<-irrefl {x} =
  ListCharₛ .Order.Strict.StrictPoset.<-irrefl
    {x = string→list x}
Strₛ .StrictPoset.<-trans {x} {y} {z} =
  ListCharₛ .Order.Strict.StrictPoset.<-trans
    {x = string→list x} {y = string→list y} {z = string→list z}

ListChar-dec-strict-total : is-decidable-strict-total-order ListCharₛ
ListChar-dec-strict-total = []<-dsto Char-dec-strict-total

Str-strict-total : is-strict-total-order Strₛ
Str-strict-total .is-strict-total-order.<-weak-linear {x} {y} {z} =
  ListChar-dec-strict-total .Order.Total.is-decidable-strict-total-order.<-weak-linear
     {x = string→list x} {y = string→list y} {z = string→list z}
Str-strict-total .is-strict-total-order.<-connex {x} {y} x≮y y≮x =
  string→list-inj $
  ListChar-dec-strict-total .Order.Total.is-decidable-strict-total-order.<-connex
    {x = string→list x} {y = string→list y} x≮y y≮x

Str-dec-strict-total : is-decidable-strict-total-order Strₛ
Str-dec-strict-total .is-decidable-strict-total-order.has-is-strict-total = Str-strict-total
Str-dec-strict-total .is-decidable-strict-total-order.dec-< {x} {y} =
  ListChar-dec-strict-total .Order.Total.is-decidable-strict-total-order.dec-<
    {x = string→list x} {y = string→list y}
Str-dec-strict-total .is-decidable-strict-total-order.has-discrete = String-is-discrete

-- interaction

Str-≤→≯ : ∀ {x y} → Strₚ .Poset._≤_ x y → ¬ (Strₛ .StrictPoset._<_ y x)
Str-≤→≯ {x} {y} =
  List-lex-≤→≯
    (λ {x} → Charₛ .StrictPoset.<-irrefl {x})
    (λ {x} {y} {z} → Charₛ .StrictPoset.<-trans {x} {y} {z})
    {xs = string→list x} {ys = string→list y}

Str-<→≱ : ∀ {x y} → Strₛ .StrictPoset._<_ x y → ¬ (Strₚ .Poset._≤_ y x)
Str-<→≱ {x} {y} =
  List-lex-<→≱
    (λ {x} → Charₛ .StrictPoset.<-irrefl {x})
    (λ {x} {y} {z} → Charₛ .StrictPoset.<-trans {x} {y} {z})
    {xs = string→list x} {ys = string→list y}
