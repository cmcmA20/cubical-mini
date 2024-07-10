{-# OPTIONS --safe #-}
module Data.Char.Path where

open import Meta.Prelude

open import Foundations.Base
open import Foundations.Equiv

open import Functions.Embedding
open import Data.Nat.Path

open import Data.Char.Base public
open import Data.Char.Properties public

char-is-set : is-set Char
char-is-set = is-embedding→is-of-hlevel 1 (set-injective→is-embedding (hlevel 2) char→ℕ-inj) (hlevel 2)
