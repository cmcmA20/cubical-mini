{-# OPTIONS --safe #-}
module Data.Bool.Instances.Discrete where

open import Foundations.Base

open import Logic.Discreteness

open import Data.Dec.Base

open import Data.Bool.Base
open import Data.Bool.Path

instance
  bool-is-discrete : is-discrete Bool
  bool-is-discrete { (false) } { (false) } = yes refl
  bool-is-discrete { (false) } { (true) }  = no false≠true
  bool-is-discrete { (true) }  { (false) } = no true≠false
  bool-is-discrete { (true) }  { (true) }  = yes refl
