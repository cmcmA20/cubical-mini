{-# OPTIONS --safe #-}
module Data.Bool.Instances.Show where

open import Meta.Show

open import Data.Bool.Base

instance
  Show-bool : Show Bool
  Show-bool .shows-prec _ false = "false"
  Show-bool .shows-prec _ true  = "true"
