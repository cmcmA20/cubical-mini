{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base
open import Foundations.Erased

open import Structures.FinSet

open import Meta.Discrete
open import Meta.Finite
open import Meta.Reflection.HLevel

open import Structures.n-Type

open import Data.Bool.Base public
open import Data.Dec.Base
open import Data.Bool.Instances.Finite
open import Data.Bool.Instances.Discrete

-- whew, painful
and-idem : ∀ x → x and x ＝ x
and-idem = witness $
  is-fin-set→exhaustible₁ (fin-set! Bool .FinSet.has-is-fin-set)
    {P = λ x → el! (x and x ＝ x)} (λ x → (x and x) ≟ x)

-- and-assoc : ∀ x y z → (x and y) and z ＝ x and (y and z)
-- and-assoc =
--   let t = is-fin-set→omniscient₁ (Bool-FinSet .FinSet.has-is-fin-set)
--   in {!!}
