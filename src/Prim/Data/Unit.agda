{-# OPTIONS --safe #-}
module Prim.Data.Unit where

open import Prim.Type
open import Agda.Builtin.Unit public

record ⊤ω : Typeω where
  instance constructor ttω
