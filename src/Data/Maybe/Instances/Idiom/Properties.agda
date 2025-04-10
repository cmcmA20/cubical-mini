{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Idiom.Properties where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Map

open import Data.Reflects.Base
open import Data.Maybe.Base
open import Data.Maybe.Path
open import Data.Maybe.Instances.Idiom
open import Data.Maybe.Instances.Map.Properties

private variable
  ℓ : Level
  A B C : Type ℓ

<*>ₘ=just : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
              {f : Maybe (A → B)} {m : Maybe A} {y : B}
          → f <*>ₘ m ＝ just y
          → Σ[ g ꞉ (A → B) ] Σ[ x ꞉ A ] (f ＝ just g) × (m ＝ just x) × (g x ＝ y)
<*>ₘ=just {f = just g}  {m = m} e =
  let (x , eq , meq) = mapₘ=just e in
  g , x , refl , eq , meq
<*>ₘ=just {f = nothing}         e = false! e

map²ₘ=just : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
              {f : A → B → C} {ma : Maybe A} {mb : Maybe B} {z : C}
           → map² f ma mb ＝ just z
           → Σ[ x ꞉ A  ] Σ[ y ꞉ B ] (ma ＝ just x) × (mb ＝ just y) × (f x y ＝ z)
map²ₘ=just {f} {ma} e =
  let (g , y , geq , eq , meq) = <*>ₘ=just {f = mapₘ f ma} e
      (x , xeq , myeq) = mapₘ=just geq
    in
  x , y , xeq , eq , happly myeq y ∙ meq

