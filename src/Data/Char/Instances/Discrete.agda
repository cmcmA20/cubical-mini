{-# OPTIONS --safe #-}
module Data.Char.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.List.Base
open import Data.Nat.Instances.Discrete

open import Data.Char.Properties

instance
  char-is-discrete : is-discrete Char
  char-is-discrete = is-discrete-injection (char→ℕ , char→ℕ-inj) discrete!

  decomp-dis-char : goal-decomposition (quote is-discrete) Char
  decomp-dis-char = decomp (quote char-is-discrete ) []
