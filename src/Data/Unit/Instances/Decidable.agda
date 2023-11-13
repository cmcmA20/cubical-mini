{-# OPTIONS --safe #-}
module Data.Unit.Instances.Decidable where

open import Foundations.Base

open import Data.Dec.Base
open import Data.Unit.Base public

instance
  ⊤-decision : Dec ⊤
  ⊤-decision = yes tt
