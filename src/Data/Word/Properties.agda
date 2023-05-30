{-# OPTIONS --safe #-}
module Data.Word.Properties where

open import Data.Word.Base public

open import Agda.Builtin.Word.Properties public
  using ()
  renaming ( primWord64ToNatInjective to word64-to-ℕ-inj)
