{-# OPTIONS --safe #-}
module Data.Bool.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete
open import Meta.HLevel

open import Data.Id

open import Data.Bool.Path

instance
  Discrete-Bool : Discrete Bool
  Discrete-Bool .Discrete._≟_ = is-discreteⁱ→is-discrete helper
    where
    helper : is-discreteⁱ Bool
    helper false false = yes reflⁱ
    helper false true  = no λ{()}
    helper true  false = no λ{()}
    helper true  true  = yes reflⁱ
