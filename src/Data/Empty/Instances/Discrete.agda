{-# OPTIONS --safe #-}
module Data.Empty.Instances.Discrete where

open import Foundations.Base

open import Meta.Decision

open import Data.Empty.Base

instance
  Discrete-⊥ : Discrete ⊥
  Discrete-⊥ .Decision.has-decidable ()
