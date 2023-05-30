{-# OPTIONS --safe #-}
module Data.Int.Base where

open import Agda.Builtin.Int public
  using
    ( pos
    ; negsuc )
  renaming ( Int to ℤ
           ; primShowInteger to show-ℤ )
