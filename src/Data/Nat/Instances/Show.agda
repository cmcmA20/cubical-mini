{-# OPTIONS --safe #-}
module Data.Nat.Instances.Show where

open import Meta.Show

open import Agda.Builtin.String
open import Data.Nat.Base

instance
  show-nat : Show ℕ
  show-nat .shows-prec _ = primShowNat
