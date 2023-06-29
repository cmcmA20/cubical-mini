{-# OPTIONS --safe #-}
module Data.Empty.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

open import Data.Dec.Base
open import Data.Empty.Base

instance opaque
  unfolding is-decidable-at-hlevel
  ⊥-decision : Decision ⊥
  ⊥-decision = no id

  ⊥-is-discrete : is-discrete ⊥
  ⊥-is-discrete ()
