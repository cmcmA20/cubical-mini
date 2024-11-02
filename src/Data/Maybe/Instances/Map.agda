{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Maybe.Base as Maybe

private variable
  ℓ : Level
  A B : Type ℓ

mapₘ : (A → B) → Maybe A → Maybe B
mapₘ f (just x) = just (f x)
mapₘ _ nothing  = nothing

instance
  Map-Maybe : Map (eff Maybe)
  Map-Maybe .map = mapₘ

  Lawful-Map-Maybe : Lawful-Map (eff Maybe)
  Lawful-Map-Maybe .map-pres-id {A} = fun-ext go where opaque
    go : (mx : Maybe A) → map refl mx ＝ mx
    go (just _) = refl
    go nothing  = refl
  Lawful-Map-Maybe .map-pres-comp {A} {f} {g} = fun-ext go where opaque
    go : (mx : Maybe A) → map (f ∙ g) mx ＝ (map f ∙ map g) mx
    go (just _) = refl
    go nothing  = refl
