{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Fin.Inductive.Base

instance
  Show-fin : ∀ {@0 m} → Show (Fin m)
  Show-fin = default-show (show-ℕ ∘ fin→ℕ)
