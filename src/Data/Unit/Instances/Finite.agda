{-# OPTIONS --safe #-}
module Data.Unit.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.FinSub.Closure
open import Data.Unit.Properties

open import Truncation.Propositional.Base

instance
  ⊤-is-fin-set : is-fin-set ⊤
  ⊤-is-fin-set = fin ∣ (is-contr→equiv-⊤ fin-1-is-contr) ₑ⁻¹ ∣₁
