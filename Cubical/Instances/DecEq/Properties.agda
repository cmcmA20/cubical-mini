{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary.Properties

open import Cubical.Instances.HLevels.Base
open import Cubical.Instances.DecEq.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  DecEq→IsSet : ⦃ DecEq A ⦄ → IsSet A
  IsOfHLevel.iohl DecEq→IsSet = Discrete→isSet _≟_
