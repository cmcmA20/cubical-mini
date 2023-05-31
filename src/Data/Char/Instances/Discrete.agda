{-# OPTIONS --safe #-}
module Data.Char.Instances.Discrete where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Discrete

open import Data.Nat.Instances.Discrete
open import Data.Id

open import Data.Char.Properties

instance
  Discrete-char : Discrete Char
  Discrete-char .Discrete._≟_ =
    is-discrete-injection (char→ℕ , char→ℕ-inj)
      (Discrete._≟_ Discrete-ℕ)
