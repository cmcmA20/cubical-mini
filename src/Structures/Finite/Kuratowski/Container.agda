{-# OPTIONS --safe #-}
module Structures.Finite.Kuratowski.Container where

open import Foundations.Base

open import Structures.Finite.ManifestEnumerable.Container

open import Truncation.Propositional.Base

private variable
  ℓ : Level
  A : Type ℓ

𝒦 : Type ℓ → Type ℓ
𝒦 A = ∥ ℰ A ∥₁
