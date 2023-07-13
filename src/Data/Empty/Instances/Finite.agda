{-# OPTIONS --safe #-}
module Data.Empty.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.Empty.Base
open import Data.FinSub.Closure

open import Truncation.Propositional.Base

instance
  ⊥-is-fin-set : is-fin-set ⊥
  ⊥-is-fin-set = fin ∣ fin-0-is-initial ₑ⁻¹ ∣₁
