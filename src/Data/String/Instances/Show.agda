{-# OPTIONS --safe #-}
module Data.String.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.String.Base

instance
  show-string : Show String
  show-string .shows-prec _ = show-str

private
  module _ where
    _ : show "abc" ＝ "\"abc\""
    _ = refl
