{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.AnonymousExistence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Fixpoint

open import Cubical.Data.Empty as ⊥
open import Cubical.Truncation.Propositional.Base

open import Cubical.Relation.Nullary.Negation

private
  variable
    ℓ ℓ′ : Level
    A : Type ℓ

SplitSupport : Type ℓ → Type ℓ
SplitSupport A = ∥ A ∥₁ → A

Collapsible : Type ℓ → Type ℓ
Collapsible A = Σ[ f ꞉ (A → A) ] 2-Constant f

Populated ⟪_⟫ : Type ℓ → Type ℓ
Populated A = (f : Collapsible A) → Fixpoint (f .fst)
⟪_⟫ = Populated

PStable : Type ℓ → Type ℓ
PStable A = ⟪ A ⟫ → A

Separated : Type ℓ → Type ℓ
Separated = onAllPaths Stable

HSeparated : Type ℓ → Type ℓ
HSeparated = onAllPaths SplitSupport

Collapsible≡ : Type ℓ → Type ℓ
Collapsible≡ = onAllPaths Collapsible

PStable≡ : Type ℓ → Type ℓ
PStable≡ = onAllPaths PStable
