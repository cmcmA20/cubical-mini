{-# OPTIONS --safe #-}
module Data.FinSum.Instances.Discrete where

open import Foundations.Base

open import Meta.Decision

import      Data.Dec.Base as Dec
open Dec
open import Data.Nat.Base
open import Data.Sum.Path

open import Data.FinSum.Base

instance
  Discrete-Fin : {n : ℕ} → Discrete (Fin n)
  Discrete-Fin .Decision.has-decidable = go where
    go : {n : ℕ} → is-discrete (Fin n)
    go {suc n} fzero    fzero    = yes refl
    go {suc n} fzero    (fsuc l) = no ⊎-disjoint
    go {suc n} (fsuc k) fzero    = no λ p → ⊎-disjoint (sym p)
    go {suc n} (fsuc k) (fsuc l) =
      Dec.map (ap fsuc) (λ ¬p p → ¬p (inr-inj p)) (go k l)
