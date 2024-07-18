{-# OPTIONS --safe #-}
module Data.Reflects.Instances.Alternative where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Alternative

open import Data.Bool.Base
open import Data.Reflects.Base
open import Data.Sum.Base

instance
  Alternative-Reflects : Alternative (eff λ T → Reflects⁰ T false)
  Alternative-Reflects .empty = ofⁿ id
  Alternative-Reflects ._<+>_ (ofⁿ a) (ofⁿ b) = ofⁿ [ a , b ]ᵤ
