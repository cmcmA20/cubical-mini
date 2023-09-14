{-# OPTIONS --safe #-}
module Data.Fin.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Fin.Base

instance
  Show-fin : ∀ {@0 m} → Show (Fin m)
  Show-fin .shows-prec _ = show-ℕ ∘ fin→ℕ
