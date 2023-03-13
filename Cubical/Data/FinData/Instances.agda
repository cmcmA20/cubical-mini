{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Instances where

open import Agda.Builtin.String using (primShowNat)

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.FinData.Base
open import Cubical.Data.FinData.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

private variable
  n : ℕ

instance
  DecEqFin : DecEq (Fin n)
  DecEq._≟_ DecEqFin = discreteFin

instance
  IsSetFin : IsSet (Fin n)
  IsOfHLevel.iohl IsSetFin = isSetFin

instance
  ShowFin : Show (Fin n)
  Show.show ShowFin k = primShowNat (toℕ k)
