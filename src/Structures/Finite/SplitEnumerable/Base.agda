{-# OPTIONS --safe #-}
module Structures.Finite.SplitEnumerable.Base where

open import Foundations.Base

open import Data.List.Base

private variable
  ℓ : Level

-- TODO List ∈
-- ℰ! : Type ℓ → Type ℓ
-- ℰ! A = Σ[ support ꞉ ListC A ] Π[ x ꞉ A ] (x ∈ support)
