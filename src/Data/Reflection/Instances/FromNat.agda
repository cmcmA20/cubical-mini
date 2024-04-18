{-# OPTIONS --safe #-}
module Data.Reflection.Instances.FromNat where

open import Foundations.Prelude

open import Meta.Literals.FromNat

open import Data.Float.Instances.FromNat
open import Data.Reflection.Fixity
open import Data.Unit.Base

instance
  Number-Precedence : From-ℕ Precedence
  Number-Precedence .From-ℕ.Constraint _ = ⊤
  Number-Precedence .from-ℕ s = related (from-ℕ s)
