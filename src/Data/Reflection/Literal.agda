{-# OPTIONS --safe #-}
module Data.Reflection.Literal where

open import Agda.Builtin.Reflection
  public
  using ( Literal ; nat ; word64 ; float ; char
        ; string ; name ; meta
        )
