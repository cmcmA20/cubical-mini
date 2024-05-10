{-# OPTIONS --safe #-}
module Data.Char.Instances.Discrete where

open import Foundations.Base

open import Logic.Discreteness

open import Data.Char.Properties
open import Data.Nat.Instances.Discrete

instance
  char-is-discrete : is-discrete Char
  char-is-discrete = ↣→is-discrete! (char→ℕ , char→ℕ-inj)
  {-# OVERLAPPING char-is-discrete #-}
