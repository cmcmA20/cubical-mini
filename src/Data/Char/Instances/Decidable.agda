{-# OPTIONS --safe #-}
module Data.Char.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Id
open import Data.Nat.Instances.Decidable

open import Data.Char.Properties

instance
  char-is-discrete : is-discrete Char
  char-is-discrete =
    is-discrete-injection (char→ℕ , char→ℕ-inj) it
