{-# OPTIONS --safe #-}
module Data.Nat.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Correspondences.Decidable

open import Data.Bool.Path hiding (_==_)
import Data.Dec.Base as Dec
open Dec
open import Data.Empty.Base
open import Data.List.Base

open import Data.Nat.Path as ℕ-path

==-refl-true : ∀ {m} → (m == m) ＝ true
==-refl-true {0} = refl
==-refl-true {suc m} = ==-refl-true {m}

==-reflects : Reflects² (_＝_) _==_
==-reflects m n with inspect (m == n)
... | false , p = Reflects′.of $ subst (λ φ → if φ then m ＝ n else m ≠ n) (sym p)
  λ m=n → true≠false $ sym (==-refl-true {m}) ∙ subst (λ φ → (m == φ) ＝ false) (sym m=n) p
... | true  , p = Reflects′.of $ subst (λ φ → if φ then m ＝ n else m ≠ n) (sym p) $
  ℕ-path.decode m n $ subst ⟦_⟧ᵇ (sym p) tt

instance
  ℕ-is-discrete : is-discrete ℕ
  ℕ-is-discrete = is-discrete-η $ reflects→decidable {n = 2} ==-reflects

  decomp-dis-ℕ : goal-decomposition (quote is-discrete) ℕ
  decomp-dis-ℕ = decomp (quote ℕ-is-discrete ) []
