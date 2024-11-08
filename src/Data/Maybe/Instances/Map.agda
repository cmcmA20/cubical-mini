{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Map where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Maybe.Base as Maybe
open import Data.Maybe.Instances.Container

private variable
  ℓ : Level
  A B : Type ℓ

open Map ⦃ ... ⦄

mapₘ : (A → B) → Maybe A → Maybe B
mapₘ f (just x) = just (f x)
mapₘ _ nothing  = nothing

instance
  Map-Maybe : Map (eff Maybe)
  Map-Maybe .map = mapₘ

  Lawful-Map-Maybe : Lawful-Map (eff Maybe)
  Lawful-Map-Maybe = Lawful-Map-AC (fun-ext ∘ go) where
    go : ∀{ℓa ℓb} {A : 𝒰 ℓa} {B : 𝒰 ℓb} (f : A → B) (mx : Maybe A) → map f mx ＝ Map-AC-default .map f mx
    go _ (just _) = refl
    go _ nothing  = refl
