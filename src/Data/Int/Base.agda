{-# OPTIONS --safe #-}
module Data.Int.Base where

open import Data.Bool.Base
open import Data.Nat.Base

open import Agda.Builtin.Int public
  using
    ( pos
    ; negsuc )
  renaming ( Int to ℤ
           ; primShowInteger to show-ℤ )

is-negative? : ℤ → Bool
is-negative? (pos _) = false
is-negative? (negsuc _) = true

is-zero-int? : ℤ → Bool
is-zero-int? (pos 0)       = true
is-zero-int? (pos (suc _)) = false
is-zero-int? (negsuc _)    = false

is-positive-int? : ℤ → Bool
is-positive-int? (pos 0)       = false
is-positive-int? (pos (suc n)) = true
is-positive-int? (negsuc _)    = false

ℤ→ℕ : ℤ → ℕ
ℤ→ℕ (pos    n) = n
ℤ→ℕ (negsuc n) = suc n
