{-# OPTIONS --safe #-}
module Data.Nat.Instances.Discrete where

open import Foundations.Base
open import Meta.Discrete

open import Data.Nat.Properties
open import Data.Id

instance
  Discrete-ℕ : Discrete ℕ
  Discrete-ℕ .Discrete._≟_ =
    is-discreteⁱ→is-discrete ℕ-is-discreteⁱ
