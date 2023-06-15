{-# OPTIONS --safe #-}
module Data.Word.Instances.Discrete where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Decision

open import Data.Nat.Instances.Discrete
open import Data.Id

open import Data.Word.Properties

instance
  Discrete-Word64 : Discrete Word64
  Discrete-Word64 .Decision.has-decidable =
    is-discrete-injection (word64→ℕ , word64→ℕ-inj)
      (Decision.has-decidable Discrete-ℕ)
