{-# OPTIONS --safe #-}
module Data.FinSub.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.FinSub.Path

open import Truncation.Propositional.Base

instance
  fin-is-fin-set : ∀ {n} → is-fin-set (Fin n)
  fin-is-fin-set = fin₁ ∣ idₑ ∣₁
