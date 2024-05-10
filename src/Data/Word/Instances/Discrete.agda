{-# OPTIONS --safe #-}
module Data.Word.Instances.Discrete where

open import Foundations.Base

open import Logic.Discreteness

open import Data.List.Base
open import Data.Nat.Instances.Discrete

open import Data.Word.Properties

instance
  word64-is-discrete : is-discrete Word64
  word64-is-discrete = ↣→is-discrete! (word64→ℕ , word64→ℕ-inj)
  {-# OVERLAPPING word64-is-discrete #-}
