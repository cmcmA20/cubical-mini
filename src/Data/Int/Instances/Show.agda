{-# OPTIONS --safe #-}
module Data.Int.Instances.Show where

open import Meta.Show

open import Agda.Builtin.Int

instance
  show-int : Show Int
  show-int .shows-prec _ = primShowInteger
