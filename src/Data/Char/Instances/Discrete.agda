{-# OPTIONS --safe #-}
module Data.Char.Instances.Discrete where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Decision

open import Data.Nat.Instances.Discrete
open import Data.Id

open import Data.Char.Properties

instance
  Discrete-char : Discrete Char
  Discrete-char .Decision.has-decidable =
    is-discrete-injection (char→ℕ , char→ℕ-inj)
      (Decision.has-decidable Discrete-ℕ)
