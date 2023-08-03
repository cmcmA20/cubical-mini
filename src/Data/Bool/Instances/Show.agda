{-# OPTIONS --safe #-}
module Data.Bool.Instances.Show where

open import Meta.Show

open import Data.Bool.Base

instance
  show-bool : Show Bool
  show-bool .shows-prec _ false = "false"
  show-bool .shows-prec _ true  = "true"
