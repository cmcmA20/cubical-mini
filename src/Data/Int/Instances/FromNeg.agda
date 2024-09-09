{-# OPTIONS --safe #-}
module Data.Int.Instances.FromNeg where

open import Foundations.Base

open import Meta.Literals.FromNeg

open import Data.Int.Base
open import Data.Unit.Base

instance
  From-neg-ℤ : From-neg ℤ
  From-neg-ℤ .From-neg.Constraint _ = ⊤
  From-neg-ℤ .from-neg n = negsuc n
