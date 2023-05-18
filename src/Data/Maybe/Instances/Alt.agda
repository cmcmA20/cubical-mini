{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Alt where

open import Foundations.Base
open import Meta.Alt

open import Data.Maybe.Base public

maybe→alt : ∀ {M : Effect} {ℓ} {A : Type ℓ}
          → ⦃ _ : Alt M ⦄ ⦃ _ : Idiom M ⦄ → Maybe A → M .Effect.₀ A
maybe→alt (just x) = pure x
maybe→alt nothing  = fail
