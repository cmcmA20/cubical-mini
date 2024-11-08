{-# OPTIONS --safe --no-exact-split #-}
module Data.Maybe.Instances.Container where

open import Foundations.Prelude

open import Meta.Effect.Base
open import Meta.Effect.Container

open import Data.Bool.Base
open import Data.Container
open import Data.Maybe.Base

Maybeᶜ : Container _ _
Maybeᶜ = Bool ▶ So

private variable
  ℓ : Level
  A : Type ℓ

maybe→cont : Maybe A → ⟦ Maybeᶜ ⟧ A
maybe→cont (just x) = true  , λ _ → x
maybe→cont nothing  = false , λ()

cont→maybe : ⟦ Maybeᶜ ⟧ A → Maybe A
cont→maybe (false , _) = nothing
cont→maybe (true  , p) = just (p oh)

maybe≃cont : Maybe A ≃ ⟦ Maybeᶜ ⟧ A
maybe≃cont = ≅→≃ $ iso maybe→cont cont→maybe (fun-ext re) (fun-ext se) where opaque
  re : (x : ⟦ Maybeᶜ ⟧ A) → maybe→cont (cont→maybe x) ＝ x
  re (false , p) = refl ,ₚ fun-ext λ()
  re (true  , p) = refl ,ₚ fun-ext λ _ → ap p prop!

  se : (x : Maybe A) → cont→maybe (maybe→cont x) ＝ x
  se (just x) = refl
  se nothing  = refl

instance
  AC-Maybe : Abstract-Container (eff Maybe)
  AC-Maybe = make-abstract-container Maybeᶜ maybe≃cont
