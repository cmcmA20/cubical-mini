{-# OPTIONS --safe #-}
module Data.Container.Instances.Map where

open import Foundations.Prelude

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Notation.Brackets

open import Data.Container.Base
open import Data.Container.Instances.Brackets

private variable
  s p : Level
  C : Container s p

instance
  Map-Container : Map (eff ⟦ C ⟧)
  Map-Container .map f = second (f ∘_)

  -- excellent
  Lawful-Map-Container : Lawful-Map (eff ⟦ C ⟧)
  Lawful-Map-Container .Lawful-Map.has-map = Map-Container
  Lawful-Map-Container .Lawful-Map.map-pres-id = refl
  Lawful-Map-Container .Lawful-Map.map-pres-comp = refl
