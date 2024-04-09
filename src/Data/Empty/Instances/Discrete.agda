{-# OPTIONS --safe #-}
module Data.Empty.Instances.Discrete where

open import Meta.Prelude

open import Correspondences.Discrete

open import Data.Dec.Base
open import Data.Empty.Base

instance
  ⊥-is-discrete : is-discrete ⊥
  ⊥-is-discrete {()}
