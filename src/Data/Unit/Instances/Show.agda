{-# OPTIONS --safe #-}
module Data.Unit.Instances.Show where

open import Meta.Show

open import Data.Unit.Base

instance
  Show-⊤ : Show ⊤
  Show-⊤ .shows-prec _ _ = "tt"
