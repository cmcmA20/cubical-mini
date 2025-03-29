{-# OPTIONS --safe #-}
module Data.List.Instances.Map.Properties where

open import Foundations.Base
open import Functions.Embedding

open import Meta.Effect.Base
open import Meta.Effect.Container
open import Meta.Effect.Map

open import Data.Reflects.Base
open import Data.List.Base as Mabye
open import Data.List.Path
open import Data.List.Instances.Map

private variable
  ℓ : Level
  A B : Type ℓ

-- ad-hoc properties

mapₗ-injective : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
                  {f : A → B}
               → Injective f → Injective (mapₗ f)
mapₗ-injective fi {x = []}     {y = []}     e = refl
mapₗ-injective fi {x = []}     {y = y ∷ ys} e = false! e
mapₗ-injective fi {x = x ∷ xs} {y = []}     e = false! e
mapₗ-injective fi {x = x ∷ xs} {y = y ∷ ys} e =
  ap² _∷_ (fi (∷-head-inj e)) (mapₗ-injective fi (∷-tail-inj e))
