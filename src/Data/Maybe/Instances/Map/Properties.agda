{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Map.Properties where

open import Foundations.Base
open import Functions.Embedding

open import Meta.Effect.Base
open import Meta.Effect.Container
open import Meta.Effect.Map

open import Data.Reflects.Base
open import Data.Maybe.Base
open import Data.Maybe.Path
open import Data.Maybe.Instances.Map

private variable
  ℓ : Level
  A B : Type ℓ

-- ad-hoc properties

mapₘ-rec : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
           {f : A → B} {g : B → C} {z : C} {m : Maybe A}
         → rec z g (mapₘ f m) ＝ rec z (g ∘ f) m
mapₘ-rec {m = just x}  = refl
mapₘ-rec {m = nothing} = refl

mapₘ-injective : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
                  {f : A → B}
               → Injective f → Injective (mapₘ f)
mapₘ-injective fi {x = just x}  {y = just y}  e = ap just (fi (just-inj e))
mapₘ-injective fi {x = just x}  {y = nothing} e = false! e
mapₘ-injective fi {x = nothing} {y = just x}  e = false! e
mapₘ-injective fi {x = nothing} {y = nothing} e = refl

mapₘ=nothing : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
                {f : A → B} {m : Maybe A}
             → mapₘ f m ＝ nothing
             → m ＝ nothing
mapₘ=nothing {f} {m = just x}  e = false! e
mapₘ=nothing {f} {m = nothing} e = refl
