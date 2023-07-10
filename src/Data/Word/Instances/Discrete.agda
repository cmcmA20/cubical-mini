{-# OPTIONS --safe #-}
module Data.Word.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.List.Base
open import Data.Nat.Instances.Discrete
open import Data.Id

open import Data.Word.Properties

word64-is-discrete : is-discrete Word64
word64-is-discrete =
  is-discrete-injection (word64→ℕ , word64→ℕ-inj) discrete!

instance
  decomp-dis-word64 : goal-decomposition (quote is-discrete) Word64
  decomp-dis-word64 = decomp (quote word64-is-discrete) []
