{-# OPTIONS --safe #-}
module Data.Reflection.Name where

open import Agda.Builtin.Reflection
  public
  using ( Name
        )
  renaming ( primQNameEquality  to _name=?_
           ; primQNameLess      to _name<?_
           ; primShowQName      to show-name
           ; primQNameFixity    to name→fixity
           ; primQNameToWord64s to name→words64
           )
