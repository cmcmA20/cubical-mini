{-# OPTIONS --safe #-}
module Data.Fin.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.FinSub.Base

open import Truncation.Propositional.Base

instance
  fin-is-fin-set : ∀ {n} → is-fin-set (Fin n)
  fin-is-fin-set = fin₁ ∣ idₑ ∣₁
