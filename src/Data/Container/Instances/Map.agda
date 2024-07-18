{-# OPTIONS --safe #-}
module Data.Container.Instances.Map where

open import Foundations.Prelude

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Notation.Brackets

open import Data.Container.Base
open import Data.Container.Instances.Brackets

instance
  Map-Container : ∀ {s p} {C : Container s p} → Map (eff ⟦ C ⟧)
  Map-Container .map f = second (f ∘_)
