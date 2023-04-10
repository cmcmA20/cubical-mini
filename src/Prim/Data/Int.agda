{-# OPTIONS --safe #-}
module Prim.Data.Int where

open import Agda.Builtin.Int public
  using
    ( pos
    ; negsuc )
  renaming ( Int to ℤ
           ; primShowInteger to show-ℤ )
