{-# OPTIONS --safe #-}
module Order.Constructions.Nat where

open import Cat.Prelude
open import Order.Base
open import Order.Constructions.Minmax
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Strict
open import Order.Total
open import Order.Trichotomous

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Dec.Tri as Tri
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Order.Inductive
open import Data.Reflects.Base as Reflects
open import Data.Sum.Base

ℕₚ : Poset 0ℓ 0ℓ
ℕₚ .Poset.Ob = ℕ
ℕₚ .Poset._≤_ = _≤_
ℕₚ .Poset.≤-thin = hlevel 1
ℕₚ .Poset.≤-refl = refl
ℕₚ .Poset.≤-trans = _∙_
ℕₚ .Poset.≤-antisym = ≤-antisym

Suc : ℕₚ ⇒ ℕₚ
Suc .hom    = suc
Suc .pres-≤ = s≤s

-- NB avoid using it in computational code
compare-nat : (m n : ℕ) → (m ≤ n) ⊎ (m ≥ n)
compare-nat 0       _ = inl z≤
compare-nat (suc m) 0 = inr z≤
compare-nat (suc m) (suc n) = [ s≤s ∙ inl , s≤s ∙ inr ]ᵤ (compare-nat m n)

ℕ-total : is-total-order ℕₚ
ℕ-total .is-total-order.compare = compare-nat

ℕ-dec-total-order : is-decidable-total-order ℕₚ
ℕ-dec-total-order .is-decidable-total-order.has-is-total = ℕ-total

instance
  ℕ-bottom : Bottom ℕₚ
  ℕ-bottom .Bottom.bot = 0
  ℕ-bottom .Bottom.has-bot _ = z≤

¬-ℕ-top : ¬ Top ℕₚ
¬-ℕ-top t = suc≰id ! where open Top t

module _ where
  open decminmax ℕ-dec-total-order

  ℕ-meets : Has-meets ℕₚ
  ℕ-meets {x} {y} .Meet.glb = min x y
  ℕ-meets {x} {y} .Meet.has-meet = min-is-meet x y

  ℕ-joins : Has-joins ℕₚ
  ℕ-joins {x} {y} .Join.lub = max x y
  ℕ-joins {x} {y} .Join.has-join = max-is-join x y


ℕₛ : StrictPoset 0ℓ 0ℓ
ℕₛ .StrictPoset.Ob = ℕ
ℕₛ .StrictPoset._<_ = _<_
ℕₛ .StrictPoset.<-thin = hlevel 1
ℕₛ .StrictPoset.<-irrefl = <-irr
ℕₛ .StrictPoset.<-trans = <-trans

<-connex : (m n : ℕ) → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
<-connex 0       0       p q = refl
<-connex 0       (suc n) p q = ⊥.rec (p (s≤s z≤))
<-connex (suc m) 0       p q = ⊥.rec (q (s≤s z≤))
<-connex (suc m) (suc n) p q = ap suc (<-connex m n (s≤s ∙ p) (s≤s ∙ q))

ℕ-dec-strict-total-order : is-decidable-strict-total-order ℕₛ
ℕ-dec-strict-total-order = discrete+dec+connnex→dec-strict-total-order auto auto <-connex
