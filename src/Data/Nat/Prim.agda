{-# OPTIONS --safe #-}
module Data.Nat.Prim where

open import Agda.Builtin.Nat public
  using
    ( zero
    ; suc
    ; _+_
    ; _-_ )
  renaming
    ( Nat to ℕ
    ; _*_ to _·_ )
