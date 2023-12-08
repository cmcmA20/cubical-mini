{-# OPTIONS --safe #-}
module Data.Float.Instances.Show where

open import Meta.Show

open import Data.Float.Base

instance
  Show-float : Show Float
  Show-float = default-show show-float
