{-# OPTIONS --safe #-}
module Data.Bool.Instances.Underlying where

open import Foundations.Base

open import Data.Bool.Base

instance
  Underlying-Bool : Underlying Bool
  Underlying-Bool .Underlying.ℓ-underlying = 0ℓ
  Underlying-Bool .Underlying.⌞_⌟ = is-true
