{-# OPTIONS --safe #-}
module Data.Reflects.Instances.Monoidal where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Monoidal

open import Data.Bool.Base
open import Data.Reflects.Base

open Monoidal ⦃ ... ⦄

instance
  Monoidal-Reflects : Monoidal (eff λ T → Reflects⁰ T true)
  Monoidal-Reflects .unit = ofʸ _
  Monoidal-Reflects ._<,>_ (ofʸ ra) (ofʸ rb) = ofʸ (ra , rb)
