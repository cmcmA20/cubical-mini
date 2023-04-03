{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Monoid.Instances.NatPlusBis where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
-- open import Cubical.Data.Nat.Instances

open import Cubical.Algebra.Monoid
--
-- open PlusBis
--
-- NatPlusBis-Monoid : Monoid ℓ-zero
-- fst NatPlusBis-Monoid = ℕ
-- MonoidStr.ε (snd NatPlusBis-Monoid) = 0
-- MonoidStr._·_ (snd NatPlusBis-Monoid) = _+'_
-- MonoidStr.isMonoid (snd NatPlusBis-Monoid) = makeIsMonoid +'-assoc +'-rid +'-lid
