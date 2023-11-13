{-# OPTIONS --safe #-}
module Data.Bool.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base
open import Data.Id

open import Data.Bool.Base

instance
  bool-is-discrete : is-discrete Bool
  bool-is-discrete = is-discreteⁱ→is-discrete helper
    where
    helper : is-discreteⁱ Bool
    helper false false = yes reflⁱ
    helper false true  = no λ()
    helper true  false = no λ()
    helper true  true  = yes reflⁱ
