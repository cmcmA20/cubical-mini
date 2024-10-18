{-# OPTIONS --safe #-}
module Data.Nat.Two where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Nat.Base

bit : Bool → ℕ
bit true  = 1
bit false = 0

odd : ℕ → Bool
odd 0       = false
odd (suc n) = not (odd n)

even : ℕ → Bool
even = not ∘ odd

_×2 : ℕ → ℕ
_×2 = _· 2

_÷2  : ℕ → ℕ
_÷2↑ : ℕ → ℕ

-- divide by 2 rounding down
zero    ÷2 = 0
(suc n) ÷2 = n ÷2↑

-- divide by 2 rounding up
zero    ÷2↑ = 0
(suc n) ÷2↑ = suc (n ÷2)
