{-# OPTIONS --safe #-}
module Data.Char.Properties where

open import Foundations.Base

open import Structures.Discrete

open import Data.Dec.Base
open import Data.Nat.Properties
open import Data.Id

open import Data.Char.Base public

open import Agda.Builtin.Char.Properties public
  using ()
  renaming ( primCharToNatInjective to char-to-nat-injectiveⁱ)
