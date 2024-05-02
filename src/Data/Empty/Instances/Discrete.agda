{-# OPTIONS --safe #-}
module Data.Empty.Instances.Discrete where

open import Meta.Prelude

open import Logic.Discreteness

open import Data.Dec.Base
open import Data.Empty.Base

instance
  ⊥-is-discrete : is-discrete ⊥
  ⊥-is-discrete {()}
