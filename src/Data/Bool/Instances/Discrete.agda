{-# OPTIONS --safe #-}
module Data.Bool.Instances.Discrete where

open import Foundations.Base
open import Meta.Discrete
open import Meta.Reflection.HLevel

open import Data.Bool.Path

instance
  Discrete-Bool : Discrete Bool
  Discrete-Bool .Discrete.has-discrete false false = yes refl
  Discrete-Bool .Discrete.has-discrete false true  = no false≠true
  Discrete-Bool .Discrete.has-discrete true  false = no λ p → false≠true (sym p)
  Discrete-Bool .Discrete.has-discrete true  true  = yes refl
