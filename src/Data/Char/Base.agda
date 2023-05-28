{-# OPTIONS --safe #-}
module Data.Char.Base where

open import Agda.Builtin.Char public
  using ( Char )
  renaming
  -- testing
  ( primIsLower    to is-lower
  ; primIsDigit    to is-digit
  ; primIsAlpha    to is-alpha
  ; primIsSpace    to is-space
  ; primIsAscii    to is-ascii
  ; primIsLatin1   to is-latin1
  ; primIsPrint    to is-print
  ; primIsHexDigit to is-hex-digit
  -- transforming
  ; primToUpper to to-upper
  ; primToLower to to-lower
  -- converting
  ; primCharToNat to to-ℕ
  ; primNatToChar to from-ℕ )

open import Agda.Builtin.String public
  using ()
  renaming ( primShowChar to show-char )
