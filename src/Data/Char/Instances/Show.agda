{-# OPTIONS --safe #-}
module Data.Char.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.Char.Base

instance
  Show-char : Show Char
  Show-char .shows-prec _ = show-char

_ : show 'a' ＝ "'a'"
_ = refl
