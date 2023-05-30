{-# OPTIONS --safe #-}
module Structures.Finite.SplitEnumerable.Container where

open import Foundations.Base

open import Containers.List.Base

private variable
  ℓ : Level

ℰ! : Type ℓ → Type ℓ
ℰ! A = Σ[ support ꞉ ⟦ ListC ⟧ A ] Π[ x ꞉ A ] (x ∈ support)
