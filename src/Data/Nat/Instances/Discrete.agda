{-# OPTIONS --safe #-}
module Data.Nat.Instances.Discrete where

open import Meta.Prelude

open import Meta.Search.Discrete

open import Structures.IdentitySystem.Interface

open import Correspondences.Decidable

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.List.Base

open import Data.Nat.Base
open import Data.Nat.Path as ℕ-path

private module ℕIS = IdSS ℕ-path.identity-system ℕ-is-set

==-reflects : Reflects (_＝_ {A = ℕ}) _==_
==-reflects m n with m == n | recall (m ==_) n
... | false | ⟪ p ⟫ = ofⁿ $ subst ⟦_⟧ᵇ p ∘ ℕIS.encode
... | true  | ⟪ p ⟫ = ofʸ $ ℕIS.decode $ subst ⟦_⟧ᵇ (sym p) tt

instance
  ℕ-is-discrete : is-discrete ℕ
  ℕ-is-discrete .is-discrete-β = reflects→decidable {2} {U = Type} ==-reflects

  decomp-dis-ℕ : goal-decomposition (quote is-discrete) ℕ
  decomp-dis-ℕ = decomp (quote ℕ-is-discrete ) []
