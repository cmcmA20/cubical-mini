{-# OPTIONS --safe #-}
module Foundations.Nat.Internal where

open import Agda.Builtin.Nat public
  using
    ( zero
    ; suc
    ; _+_
    ; _-_ )
  renaming
    ( Nat to ℕ
    ; _*_ to _·_ )
