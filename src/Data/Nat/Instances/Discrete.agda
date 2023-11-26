{-# OPTIONS --safe #-}
module Data.Nat.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete
open import Meta.Underlying

open import Correspondences.Decidable

open import Data.Bool.Base as Bool
open import Data.Bool.Path hiding (_==_)
import Data.Dec.Base as Dec
open Dec
open import Data.Empty.Base
open import Data.List.Base

open import Data.Nat.Path as ℕ-path

==-refl-true : ∀ {m} → (m == m) ＝ true
==-refl-true {0}     = refl
==-refl-true {suc m} = ==-refl-true {m}

==-reflects : Reflects (_＝_ {A = ℕ}) _==_
==-reflects m n with m == n | recall (m ==_) n
... | false | ⟪ p ⟫ = ofⁿ λ m=n →
  true≠false (sym (==-refl-true {n}) ∙ subst (λ φ → (φ == n) ＝ false) m=n p)
... | true  | ⟪ p ⟫ = ofʸ $ ℕ-path.decode m n $ subst (Bool.elim _ _) (sym p) tt

instance
  ℕ-is-discrete : is-discrete ℕ
  ℕ-is-discrete .is-discrete-β = reflects→decidable {2} {U = Type} ==-reflects

  decomp-dis-ℕ : goal-decomposition (quote is-discrete) ℕ
  decomp-dis-ℕ = decomp (quote ℕ-is-discrete ) []
