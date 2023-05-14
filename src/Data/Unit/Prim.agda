{-# OPTIONS --safe #-}
module Data.Unit.Prim where

open import Foundations.Type
open import Agda.Builtin.Unit public

record ⊤ω : Typeω where
  instance constructor ttω
