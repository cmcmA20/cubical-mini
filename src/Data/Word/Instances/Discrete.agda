{-# OPTIONS --safe #-}
module Data.Word.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Nat.Instances.Discrete

open import Data.Word.Properties

instance
  word64-is-discrete : is-discrete Word64
  word64-is-discrete =
    is-discrete-injection (word64→ℕ , word64→ℕ-inj) discrete!
