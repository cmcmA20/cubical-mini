{-# OPTIONS --safe #-}
module Data.String.Instances.Show where

open import Foundations.Base

open import Meta.Show

open import Data.String.Base

instance
  string-show : Show String
  string-show .Show.shows-prec _ = show-str
