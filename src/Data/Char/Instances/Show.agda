{-# OPTIONS --safe #-}
module Data.Char.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Agda.Builtin.String
open import Data.Char.Base

instance
  show-char : Show Char
  show-char .shows-prec _ = primShowChar

private
  module _ where
    _ : show 'a' ＝ "'a'"
    _ = refl
