{-# OPTIONS --safe #-}
module Data.String.Base where

open import Agda.Builtin.String public
  using( String )
  renaming
    ( primStringAppend   to infixr 5 _++ₛ_
    ; primStringUncons   to uncons
    ; primStringToList   to string→list
    ; primStringFromList to list→string
    ; primShowString     to show-string
    ; primShowNat        to show-ℕ )
