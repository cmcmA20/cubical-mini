{-# OPTIONS --safe #-}
module Prim.Data.Sigma where

open import Agda.Builtin.Sigma public

infix 2 Σ-syntax
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ꞉ A ] B
