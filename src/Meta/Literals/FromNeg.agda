{-# OPTIONS --safe #-}
module Meta.Literals.FromNeg where

open import Agda.Builtin.FromNeg public
  using ( Negative )
  renaming ( fromNeg to from-neg )
