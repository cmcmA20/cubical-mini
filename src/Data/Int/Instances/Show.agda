{-# OPTIONS --safe #-}
module Data.Int.Instances.Show where

open import Meta.Show

open import Data.Int.Base

instance
  Show-ℤ : Show ℤ
  Show-ℤ .shows-prec _ = show-ℤ
