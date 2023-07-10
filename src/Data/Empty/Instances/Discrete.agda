{-# OPTIONS --safe #-}
module Data.Empty.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base
open import Data.Empty.Base

instance opaque
  unfolding is-discrete
  ⊥-is-discrete : is-discrete ⊥
  ⊥-is-discrete ()
