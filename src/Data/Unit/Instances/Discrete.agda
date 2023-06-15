{-# OPTIONS --safe #-}
module Data.Unit.Instances.Discrete where

open import Foundations.Base

open import Meta.Decision

open import Data.Dec.Base
open import Data.Unit.Base public

instance
  Discrete-⊤ : Discrete ⊤
  Discrete-⊤ .Decision.has-decidable tt tt = yes refl
