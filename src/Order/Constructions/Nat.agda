{-# OPTIONS --safe #-}
module Order.Constructions.Nat where

open import Cat.Prelude
open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top

open import Data.Nat.Base
open import Data.Nat.Order.Inductive

ℕₚ : Poset 0ℓ 0ℓ
ℕₚ .Poset.Ob = ℕ
ℕₚ .Poset._≤_ = _≤_
ℕₚ .Poset.≤-thin = hlevel 1
ℕₚ .Poset.≤-refl = refl
ℕₚ .Poset.≤-trans = _∙_
ℕₚ .Poset.≤-antisym = ≤-antisym

ℕ-bottom : Bottom ℕₚ
ℕ-bottom .Bottom.bot = 0
ℕ-bottom .Bottom.has-bot _ = z≤

¬-ℕ-top : ¬ Top ℕₚ
¬-ℕ-top t = suc≰id ! where open Top t

-- TODO move this out
private
  min≤l : ∀ x y → min x y ≤ x
  min≤l 0       _ = z≤
  min≤l (suc x) 0 = z≤
  min≤l (suc x) (suc y) = s≤s (min≤l x y)

  min≤r : ∀ x y → min x y ≤ y
  min≤r 0       _ = z≤
  min≤r (suc x) 0 = z≤
  min≤r (suc x) (suc y) = s≤s (min≤r x y)

  min-univ : ∀ lb x y → lb ≤ x → lb ≤ y → lb ≤ min x y
  min-univ 0 x y p q = z≤
  min-univ (suc lb) (suc x) (suc y) p q = s≤s (min-univ lb x y (≤-peel p) (≤-peel q))

  l≤max : ∀ x y → x ≤ max x y
  l≤max 0       y = z≤
  l≤max (suc x) 0 = refl
  l≤max (suc x) (suc y) = s≤s (l≤max x y)

  r≤max : ∀ x y → y ≤ max x y
  r≤max 0       y = refl
  r≤max (suc x) 0 = z≤
  r≤max (suc x) (suc y) = s≤s (r≤max x y)

  max-univ : ∀ ub x y → x ≤ ub → y ≤ ub → max x y ≤ ub
  max-univ ub 0       y p q = q
  max-univ ub (suc x) 0 p q = p
  max-univ (suc ub) (suc x) (suc y) p q = s≤s (max-univ ub x y (≤-peel p) (≤-peel q))

ℕ-meets : Has-meets ℕₚ
ℕ-meets {x} {y} .Meet.glb = min x y
ℕ-meets {x} {y} .Meet.has-meet .is-meet.meet≤l = min≤l x y
ℕ-meets {x} {y} .Meet.has-meet .is-meet.meet≤r = min≤r x y
ℕ-meets {x} {y} .Meet.has-meet .is-meet.greatest lb = min-univ lb x y

ℕ-joins : Has-joins ℕₚ
ℕ-joins {x} {y} .Join.lub = max x y
ℕ-joins {x} {y} .Join.has-join .is-join.l≤join = l≤max x y
ℕ-joins {x} {y} .Join.has-join .is-join.r≤join = r≤max x y
ℕ-joins {x} {y} .Join.has-join .is-join.least ub = max-univ ub x y
