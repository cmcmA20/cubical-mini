{-# OPTIONS --safe #-}
module Cubical.Interface.HLevels.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels public

open import Cubical.Data.Nat.Base

open import Cubical.Reflection.RecordEquiv

private variable ℓ : Level

record IsOfHLevel (n : ℕ) (A : Type ℓ) : Type ℓ where
  constructor mkIsOfHLevel
  field iohl : isOfHLevel n A
open IsOfHLevel

unquoteDecl IsOfHLevelIsoΣ = declareRecordIsoΣ IsOfHLevelIsoΣ (quote IsOfHLevel)

IsOfHLevel≡ : {n : ℕ} {A : Type ℓ} {x y : IsOfHLevel n A} → x .iohl ≡ y .iohl → x ≡ y
IsOfHLevel≡ {x = mkIsOfHLevel _} {y = mkIsOfHLevel _} p = cong mkIsOfHLevel p

IsContr : Type ℓ → Type ℓ
IsContr = IsOfHLevel 0

IsProp : Type ℓ → Type ℓ
IsProp = IsOfHLevel 1

IsSet : Type ℓ → Type ℓ
IsSet = IsOfHLevel 2

IsGroupoid : Type ℓ → Type ℓ
IsGroupoid = IsOfHLevel 3
