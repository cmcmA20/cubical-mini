{-# OPTIONS --safe #-}
module Data.Empty.Instances.Decidable where

open import Foundations.Base

open import Data.Dec.Base
open import Data.Empty.Base

instance
  ⊥-decision : Dec ⊥
  ⊥-decision = no id
