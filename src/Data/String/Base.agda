{-# OPTIONS --safe #-}
module Data.String.Base where

open import Agda.Builtin.String public
  using( String )
  renaming
    ( primStringUncons   to uncons
    ; primStringToList   to string→list
    ; primStringFromList to list→string
    ; primShowString     to show-str
    ; primShowNat        to show-ℕ )

infixr 5 _++ₛ_
_++ₛ_ : String → String → String
_++ₛ_ = Agda.Builtin.String.primStringAppend
