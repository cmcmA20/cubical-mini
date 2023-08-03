{-# OPTIONS --safe #-}
module Data.Unit.Instances.Show where

open import Meta.Show

open import Data.Unit.Base

instance
  show-unit : Show ⊤
  show-unit .shows-prec _ tt = "tt"
