{-# OPTIONS --safe #-}
module Cubical.Cardinality.Finite.SplitEnumerable.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Container.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.SumFin.Base
open import Cubical.Data.Sigma
open import Cubical.Data.List.Container renaming (List′ to List)

open import Cubical.Functions.Surjection

private variable
  ℓ : Level
  A : Type ℓ

ℰ! : Type ℓ → Type ℓ
ℰ! A = Σ[ support ꞉ List A ] ((x : A) → x ∈ support)

kek : ℰ! A ≃ Σ ℕ λ n → Fin n ↠! A
kek = Σ-assoc-≃
