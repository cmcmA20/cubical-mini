{-# OPTIONS --safe #-}
module Cubical.Instances.HLevels.Data.Empty where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty

open import Cubical.Instances.HLevels.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

instance
  IsProp⊥ : IsProp ⊥
  IsOfHLevel.iohl IsProp⊥ = isProp⊥

  IsProp⊥* : IsProp {ℓ} ⊥*
  IsOfHLevel.iohl IsProp⊥* = isProp⊥*

  IsContr⊥→A : IsContr (⊥ → A)
  IsOfHLevel.iohl IsContr⊥→A = isContr⊥→A

  IsContrΠ⊥ : {A : ⊥ → Type ℓ} → IsContr ((x : ⊥) → A x)
  IsOfHLevel.iohl IsContrΠ⊥ = isContrΠ⊥

  IsContrΠ⊥* : {A : ⊥* {ℓ} → Type ℓ′} → IsContr ((x : ⊥*) → A x)
  IsOfHLevel.iohl IsContrΠ⊥* = isContrΠ⊥*
