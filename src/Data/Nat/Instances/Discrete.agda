{-# OPTIONS --safe #-}
module Data.Nat.Instances.Discrete where

open import Meta.Prelude

open import Structures.IdentitySystem.Interface

open import Correspondences.Decidable
open import Correspondences.Discrete

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec

open import Data.Nat.Base
open import Data.Nat.Path as ℕ-path

private module ℕIS = IdSS ℕ-path.identity-system (hlevel 2)

==-reflects : Reflects (_＝_ {A = ℕ}) _==_
==-reflects m n with m == n | recall (m ==_) n
... | false | ⟪ p ⟫ = ofⁿ $ subst is-true p ∘ ℕIS.encode
... | true  | ⟪ p ⟫ = ofʸ $ ℕIS.decode $ subst is-true (sym p) tt

instance
  ℕ-is-discrete : is-discrete ℕ
  ℕ-is-discrete = reflects→decidable {2} {U = Type} ==-reflects
