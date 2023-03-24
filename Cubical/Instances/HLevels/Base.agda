{-# OPTIONS --safe #-}
module Cubical.Instances.HLevels.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Base

open import Cubical.Reflection.RecordEquiv

open Iso

private variable
  ℓ : Level
  A : Type ℓ
  h : HLevel

record IsOfHLevel (h : ℕ) (A : Type ℓ) : Type ℓ where
  field iohl : isOfHLevel h A
open IsOfHLevel ⦃ ... ⦄ public

unquoteDecl IsOfHLevelIsoΣ = declareRecordIsoΣ IsOfHLevelIsoΣ (quote IsOfHLevel)

IsOfHLevelExt : {x y : IsOfHLevel h A} → x .iohl ≡ y .iohl → x ≡ y
IsOfHLevelExt = cong (IsOfHLevelIsoΣ .inv)

IsContr : Type ℓ → Type ℓ
IsContr = IsOfHLevel 0

IsProp : Type ℓ → Type ℓ
IsProp = IsOfHLevel 1

IsSet : Type ℓ → Type ℓ
IsSet = IsOfHLevel 2

IsGroupoid : Type ℓ → Type ℓ
IsGroupoid = IsOfHLevel 3
