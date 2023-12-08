{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Alt where

open import Foundations.Base

open import Meta.Effect.Alt

open import Data.Maybe.Base

private variable
  ℓ : Level
  A : Type ℓ
  M : Effect

maybe→alt : (let module M = Effect M)
            ⦃ _ : Alt M ⦄ ⦃ _ : Idiom M ⦄
          → Maybe A → M.₀ A
maybe→alt (just x) = pure x
maybe→alt nothing  = fail

instance
  Alt-Maybe : Alt (eff Maybe)
  Alt-Maybe .Alt.fail = nothing
  Alt-Maybe .Alt._<|>_ (just x) _ = just x
  Alt-Maybe .Alt._<|>_ nothing  y = y
