{-# OPTIONS --safe #-}
module Data.Empty.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.List.Base

⊥-decision : Dec ⊥
⊥-decision = no id

instance
  decomp-dec-⊥ : goal-decomposition (quote Dec) ⊥
  decomp-dec-⊥ = decomp (quote ⊥-decision) []
