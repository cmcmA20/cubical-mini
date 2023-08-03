{-# OPTIONS --safe #-}
module Data.Float.Instances.Show where

open import Meta.Show

open import Agda.Builtin.Float

instance
  show-floatᵢ : Show Float
  show-floatᵢ .shows-prec _ = primShowFloat
