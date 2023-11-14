{-# OPTIONS --safe #-}
module Data.Fin.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.Nat.Base
open import Data.FinSub.Base
open import Data.List.Base

open import Truncation.Propositional.Base

private variable n : ℕ

instance
  fin-is-fin-set : is-fin-set (Fin n)
  fin-is-fin-set = fin₁ ∣ idₑ ∣₁

  decomp-fin-fin : goal-decomposition (quote is-fin-set) (Fin n)
  decomp-fin-fin = decomp (quote fin-is-fin-set) []
