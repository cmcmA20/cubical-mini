{-# OPTIONS --safe #-}
module Data.Nat.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete
open import Meta.Underlying

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
... | false | ⟪ p ⟫ = ofⁿ $ subst (Bool.elim _ _) p ∘ ℕIS.encode
... | true  | ⟪ p ⟫ = ofʸ $ ℕIS.decode $ subst (Bool.elim _ _) (sym p) tt

instance
  ℕ-is-discrete : is-discrete ℕ
  ℕ-is-discrete .is-discrete-β = reflects→decidable {2} {U = Type} ==-reflects

  decomp-dis-ℕ : goal-decomposition (quote is-discrete) ℕ
  decomp-dis-ℕ = decomp (quote ℕ-is-discrete ) []
