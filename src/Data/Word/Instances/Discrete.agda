{-# OPTIONS --safe #-}
module Data.Word.Instances.Discrete where

open import Foundations.Base
open import Foundations.Equiv

open import Correspondences.Nullary.Decidable

open import Data.Nat.Instances.Discrete
open import Data.Id

open import Data.Word.Properties

instance
  word64-is-discrete : is-discrete Word64
  word64-is-discrete =
    is-discrete-injection (word64→ℕ , word64→ℕ-inj) it
