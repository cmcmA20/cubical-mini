{-# OPTIONS --safe #-}
module Structures.FinSet where

open import Foundations.Base
open import Foundations.Sigma
open import Foundations.Univalence

open import Meta.Idiom
open import Meta.Search.HLevel
open import Meta.Underlying public

open import Structures.Base
open import Structures.n-Type

open import Correspondences.Nullary.Finite.Bishop
open import Correspondences.Nullary.Decidable
open import Correspondences.Nullary.Omniscience
open import Correspondences.Unary.Decidable

import      Data.Dec.Base as Dec
open Dec
open import Data.Dec.Properties
open import Data.Dec.Instances.HLevel
open import Data.Empty
open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Data.Vec.Correspondences.Unary.Any

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

opaque
  FinSet : (ℓ : Level) → Type (ℓsuc ℓ)
  FinSet ℓ = Type-with (property is-fin-set λ _ → is-fin-set-is-prop)

  mk-FinSet : (A : Type ℓ) → _ → FinSet ℓ
  mk-FinSet A A-fin = A , A-fin

  FinSet-Carrier : FinSet ℓ → Type ℓ
  FinSet-Carrier = fst

-- TODO refactor after automation's ready
fin-set! : (A : Type ℓ) → ⦃ is-fin-set A ⦄ → FinSet ℓ
fin-set! A = mk-FinSet A it

instance
  Underlying-FinSet : Underlying (FinSet ℓ)
  Underlying-FinSet {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-FinSet .⌞_⌟ = FinSet-Carrier
