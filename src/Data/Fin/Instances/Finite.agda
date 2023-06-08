{-# OPTIONS --safe #-}
module Data.Fin.Instances.Finite where

open import Foundations.Base

open import Meta.Finite

open import Data.Fin.Base

open import Truncation.Propositional.Base

instance
  Finite-Fin : ∀ {n} → Finite (Fin n)
  Finite-Fin = fin ∣ idₑ ∣₁
