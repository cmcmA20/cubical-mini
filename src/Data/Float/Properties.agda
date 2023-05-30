{-# OPTIONS --safe #-}
module Data.Float.Properties where

open import Data.Float.Base public

open import Agda.Builtin.Float.Properties public
  using ()
  renaming (primFloatToWord64Injective to float-to-word64-inj)
