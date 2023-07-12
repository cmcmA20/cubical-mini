{-# OPTIONS --safe #-}
module Data.Unit.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Dec.Base
open import Data.List.Base
open import Data.Unit.Base public

⊤-decision : Dec ⊤
⊤-decision = yes tt

instance
  decomp-dec-⊤ : goal-decomposition (quote Dec) ⊤
  decomp-dec-⊤ = decomp (quote ⊤-decision) []
