{-# OPTIONS --safe #-}
module Cubical.Interface.Show where

open import Cubical.Foundations.Prelude
open import Agda.Builtin.String
open import Agda.Builtin.String using (String) renaming (primStringAppend to _++_) public

-- don't use for prettyprinting
record Show {ℓᵃ} (A : Type ℓᵃ) : Type ℓᵃ where
  field show : A → String
