{-# OPTIONS --safe #-}
module Data.String.Base where

open import Agda.Builtin.String public
  using( String )
  renaming
    ( primStringUncons   to uncons
    ; primStringToList   to to-list
    ; primStringFromList to from-list
    ; primStringAppend   to concat-str
    ; primShowString     to show-str
    ; primShowNat        to show-ℕ )
