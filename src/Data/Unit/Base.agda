{-# OPTIONS --safe #-}
module Data.Unit.Base where

open import Prim.Type
open import Prim.Data.Unit public

record ⊤ω : Typeω where
  instance constructor ttω
