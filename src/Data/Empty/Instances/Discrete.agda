{-# OPTIONS --safe #-}
module Data.Empty.Instances.Discrete where

open import Foundations.Base

open import Correspondences.Nullary.Decidable

open import Data.Empty.Base

instance opaque
  unfolding is-decidable-at-hlevel
  ⊥-is-discrete : is-discrete ⊥
  ⊥-is-discrete ()
