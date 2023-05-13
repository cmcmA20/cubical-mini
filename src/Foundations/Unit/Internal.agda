{-# OPTIONS --safe #-}
module Foundations.Unit.Internal where

open import Foundations.Type.Internal
open import Agda.Builtin.Unit public

record ⊤ω : Typeω where
  instance constructor ttω
