{-# OPTIONS --safe #-}
module Data.Empty.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.List.Base

opaque
  unfolding is-discrete
  ⊥-is-discrete : is-discrete ⊥
  ⊥-is-discrete ()

instance
  decomp-dis-⊥ : goal-decomposition (quote is-discrete) ⊥
  decomp-dis-⊥ = decomp (quote ⊥-is-discrete) []
