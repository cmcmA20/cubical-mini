{-# OPTIONS --safe #-}
module Data.Container.Instances.Map where

open import Foundations.Prelude

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Container.Base
open import Data.Container.Instances.Brackets

private variable
  s p : Level
  C : Container s p

open Map ⦃ ... ⦄
open Lawful-Map ⦃ ... ⦄

instance
  Map-Container : Map (eff ⟦ C ⟧)
  Map-Container .map f = second (f ∘_)

  -- excellent
  Lawful-Map-Container : Lawful-Map (eff ⟦ C ⟧)
  Lawful-Map-Container .Lawful-Map.map-pres-id = refl
  Lawful-Map-Container .Lawful-Map.map-pres-comp = refl
