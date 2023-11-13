{-# OPTIONS --safe #-}
module Data.Empty.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Empty.Base

instance
  ⊥-is-discrete : is-discrete ⊥
  ⊥-is-discrete .is-discrete-β ()
