{-# OPTIONS --safe #-}
module Data.Word.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Nat.Instances.Decidable
open import Data.Id

open import Data.Word.Properties

instance
  word64-is-discrete : is-discrete Word64
  word64-is-discrete =
    is-discrete-injection (word64→ℕ , word64→ℕ-inj) it
