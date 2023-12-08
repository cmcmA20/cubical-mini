{-# OPTIONS --safe #-}
module Meta.Literals.FromNeg where

open import Agda.Builtin.FromNeg public
  using ()
  renaming ( Negative to From-neg
           ; fromNeg to from-neg )
