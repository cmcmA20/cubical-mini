{-# OPTIONS --safe #-}
module Cubical.HITs.Interval.Base where

open import Cubical.Foundations.Prelude

data Interval : Type where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one

private variable
  ℓ : Level
  A : Type ℓ

elim : (A : Interval → Type ℓ)
       (x : A zero) (y : A one) (p : PathP (λ i → A (seg i)) x y)
       (x : Interval)
     → A x
elim A x y p zero    = x
elim A x y p one     = y
elim A x y p (seg i) = p i
