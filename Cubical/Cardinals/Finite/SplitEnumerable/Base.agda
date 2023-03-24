{-# OPTIONS --safe #-}
module Cubical.Cardinals.Finite.SplitEnumerable.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Container.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.SumFin.Base
open import Cubical.Data.Sigma

open import Cubical.Container.Instances.List

open import Cubical.Functions.Surjection

private variable
  ℓ : Level
  A : Type ℓ

ℰ! : Type ℓ → Type ℓ
ℰ! A = Σ[ support ꞉ List A ] Π[ x ꞉ A ] (x ∈ support)

ℰ!≃Fin↠! : ℰ! A ≃ Σ[ n ꞉ ℕ ] (Fin n ↠! A)
ℰ!≃Fin↠! = Σ-assoc-≃
