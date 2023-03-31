{-# OPTIONS --safe #-}
module Cubical.Data.Digit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.List.Base

Digit : ℕ → Type
Digit n = Fin n

Decimal = Digit 10
Bit = Digit 2

0b : Bit
0b = zero

1b : Bit
1b = suc zero

Expansion : ℕ → Type
Expansion base = List (Digit base)
