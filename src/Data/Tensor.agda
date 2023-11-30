{-# OPTIONS --safe #-}
open import Foundations.Base
open import Data.Fin.Interface
open import Data.Nat.Base using (ℕ)

module Data.Tensor {F : @0 ℕ → Type} (fin-impl : FinI F) where

open import Data.Tensor.Base fin-impl       public
-- open import Data.Tensor.Properties fin-impl public

open import Data.Tensor.Instances.FromProduct fin-impl public
