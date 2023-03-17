{-# OPTIONS --safe #-}
module Cubical.Data.Empty.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty.Base
open import Cubical.Data.Empty.Properties
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Interface.DecEq
open import Cubical.Interface.Finite
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

instance
  DecEq⊥ : DecEq ⊥
  DecEq._≟_ DecEq⊥ ()


instance
  Finite⊥ : Finite ⊥
  Finite.isFinite Finite⊥ = 0 , ∣ uninhabEquiv (λ x → x) (λ x → x) ∣₁


instance
  Show⊥ : Show ⊥
  Show.show Show⊥ ()


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
