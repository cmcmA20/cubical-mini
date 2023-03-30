{-# OPTIONS --safe --overlapping-instances --instance-search-depth=2 #-}
module Cubical.Algebra.Monoid.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat

open import Cubical.Algebra.Monoid.Base

open import Cubical.Instances.DecEq

NatMonoid : Monoid ℓ-zero
fst NatMonoid = ℕ
MonoidStr.ε (snd NatMonoid) = 0
MonoidStr._·_ (snd NatMonoid) = _+_
MonoidStr.isMonoid (snd NatMonoid) = makeIsMonoid +-assoc +-zero (λ _ → refl)
