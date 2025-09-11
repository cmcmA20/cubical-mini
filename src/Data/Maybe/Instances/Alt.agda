{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Alt where

open import Foundations.Base

open import Meta.Effect.Choice
open import Meta.Effect.Alt
open import Meta.Effect.Base
open import Meta.Effect.Idiom

open import Data.Maybe.Base

private variable
  ℓ : Level
  A : Type ℓ
  M : Effect

open Choice ⦃ ... ⦄
open Alt ⦃ ... ⦄
open Idiom ⦃ ... ⦄

maybe→alt : (let module M = Effect M)
            ⦃ _ : Alt M ⦄ ⦃ _ : Idiom M ⦄
          → Maybe A → M.₀ A
maybe→alt (just x) = pure x
maybe→alt nothing  = fail

instance
  Choice-Maybe : Choice (eff Maybe)
  Choice-Maybe ._<|>_ (just x) _ = just x
  Choice-Maybe ._<|>_ nothing  y = y

  Alt-Maybe : Alt (eff Maybe)
  Alt-Maybe .fail = nothing
