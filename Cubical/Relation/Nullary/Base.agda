{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Fixpoint

open import Cubical.Truncation.Propositional.Base

private
  variable
    ℓ  : Level

-- reexport propositional truncation for uniformity
open Cubical.Truncation.Propositional.Base
  using (∥_∥₁) public

onAllPaths : (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
onAllPaths S A = (x y : A) → S (x ≡ y)
