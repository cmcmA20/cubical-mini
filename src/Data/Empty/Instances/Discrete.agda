{-# OPTIONS --safe #-}
module Data.Empty.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete

open import Data.Empty.Base

instance
  Discrete-⊥ : Discrete ⊥
  Discrete-⊥ .Discrete._≟_ ()
