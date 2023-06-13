{-# OPTIONS --safe #-}
module Data.Unit.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete

open import Data.Unit.Base public

instance
  Discrete-⊤ : Discrete ⊤
  Discrete-⊤ .Discrete._≟_ tt tt = yes refl
