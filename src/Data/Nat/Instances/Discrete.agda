{-# OPTIONS --safe #-}
module Data.Nat.Instances.Discrete where

open import Meta.Prelude

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Nat.Base
open import Data.Nat.Path

private module ℕIS = IdSS ℕ-identity-system (hlevel 2)

==-reflects : Reflects (Path ℕ) _==_
==-reflects m n with m == n | recall (m ==_) n
... | false | ⟪ p ⟫ = ofⁿ $ substₚ is-true p ∘ ℕIS.encode
... | true  | ⟪ p ⟫ = ofʸ $ ℕIS.decode $ substₚ is-true (sym p) tt

instance
  ℕ-is-discrete : is-discrete ℕ
  ℕ-is-discrete = reflects→decidable {2} {U = Type} ==-reflects
  {-# OVERLAPPING ℕ-is-discrete #-}
