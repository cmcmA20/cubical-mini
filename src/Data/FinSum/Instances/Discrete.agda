{-# OPTIONS --safe #-}
module Data.FinSum.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base as Dec
open import Data.List.Base
open import Data.Nat.Base
open import Data.Sum.Path

open import Data.FinSum.Base

private variable n : ℕ

instance
  fin-is-discrete : is-discrete (Fin n)
  fin-is-discrete {suc _} .is-discrete-β fzero    fzero    = yes refl
  fin-is-discrete {suc _} .is-discrete-β fzero    (fsuc l) = no ⊎-disjoint
  fin-is-discrete {suc _} .is-discrete-β (fsuc k) fzero    = no $ ⊎-disjoint ∘ sym
  fin-is-discrete {suc _} .is-discrete-β (fsuc k) (fsuc l) =
    Dec.map (ap fsuc) (_∘ inr-inj) (fin-is-discrete .is-discrete-β k l)

  decomp-dis-fin : goal-decomposition (quote is-discrete) (Fin n)
  decomp-dis-fin = decomp (quote fin-is-discrete) []
