{-# OPTIONS --safe #-}
module Data.Bool.Instances.Discrete where

open import Foundations.Base

open import Meta.Decision
open import Meta.HLevel

open import Data.Dec.Base
open import Data.Id

open import Data.Bool.Path

instance
  Discrete-Bool : Discrete Bool
  Discrete-Bool .Decision.has-decidable = is-discreteⁱ→is-discrete helper
    where
    helper : is-discreteⁱ Bool
    helper false false = yes reflⁱ
    helper false true  = no λ{()}
    helper true  false = no λ{()}
    helper true  true  = yes reflⁱ
