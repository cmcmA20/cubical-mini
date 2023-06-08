{-# OPTIONS --safe #-}
module Data.FinSum.Instances.Finite where

open import Foundations.Base

open import Meta.Finite

open import Data.FinSum.Path

open import Truncation.Propositional.Base

instance
  Finite-Fin : ∀ {n} → Finite (Fin n)
  Finite-Fin = fin ∣ sum-fin≃finⁱ ∣₁
