{-# OPTIONS --safe #-}
module Data.Container.Instances.Map where

open import Foundations.Prelude

open import Meta.Brackets
open import Meta.Effect.Idiom

open import Data.Container.Base
open import Data.Container.Instances.Brackets

instance
  Map-Container : ∀ {s p} {C : Container s p} → Map (eff ⟦ C ⟧)
  Map-Container .Map.map f = second (f ∘_)
