{-# OPTIONS --safe #-}
module Data.FinSum.Instances.Finite where

open import Foundations.Base

open import Meta.Search.Finite.Bishop

open import Data.FinSum.Path

open import Truncation.Propositional.Base

-- FIXME
-- instance
--   fin-is-fin-set : ∀ {n} → is-fin-set (Fin n)
--   fin-is-fin-set = fin ∣ sum-fin≃finⁱ ∣₁
