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

char-is-discreteⁱ : is-discreteⁱ Char
char-is-discreteⁱ x y with ℕ-is-discreteⁱ (to-ℕ x) (to-ℕ y)
... | yes p = yes $ char-to-nat-injectiveⁱ _ _ p
... | no ¬p = no λ p → ¬p (apⁱ to-ℕ p)
