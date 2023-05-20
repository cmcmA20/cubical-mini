{-# OPTIONS --safe #-}
module Data.Unit.Base where

open import Foundations.Base

open import Agda.Builtin.Unit public

record ⊤ω : Typeω where
  instance constructor ttω
