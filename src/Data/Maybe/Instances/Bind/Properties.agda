{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Bind.Properties where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Map

open import Data.Reflects.Base
open import Data.Maybe.Base
open import Data.Maybe.Path
open import Data.Maybe.Instances.Bind
open import Data.Sum.Base

private variable
  ℓ : Level
  A B C : Type ℓ

bindₘ=nothing : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
                  {f : A → Maybe B} {m : Maybe A}
              → bindₘ m f ＝ nothing
              → (m ＝ nothing) ⊎ (Σ[ x ꞉ A ] (m ＝ just x) × (f x ＝ nothing))
bindₘ=nothing {m = just x}  e = inr (x , refl , e)
bindₘ=nothing {m = nothing} e = inl refl

bindₘ=just : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
               {f : A → Maybe B} {m : Maybe A} {y : B}
           → bindₘ m f ＝ just y
           → (Σ[ x ꞉ A ] (m ＝ just x) × (f x ＝ just y))
bindₘ=just {m = just x}  e = x , refl , e
bindₘ=just {m = nothing} e = false! e
