{-# OPTIONS --safe #-}
module Data.Maybe.Instances where

open import Foundations.Base
open import Meta.Idiom
open import Meta.Bind
open import Meta.Alt
open import Meta.Traverse

open import Data.Maybe.Base

instance
  Map-Maybe : Map (eff Maybe)
  Map-Maybe .Map._<$>_ = map

  Idiom-Maybe : Idiom (eff Maybe)
  Idiom-Maybe .Idiom.pure = just
  Idiom-Maybe .Idiom._<*>_ = λ where
    (just f) (just x) → just (f x)
    _ _ → nothing

  Bind-Maybe : Bind (eff Maybe)
  Bind-Maybe .Bind._>>=_ = extend

  Traverse-Maybe : Traverse (eff Maybe)
  Traverse-Maybe .Traverse.traverse f (just x) = just <$> f x
  Traverse-Maybe .Traverse.traverse f nothing  = pure nothing

maybe→alt : ∀ {M : Effect} {ℓ} {A : Type ℓ}
          → ⦃ _ : Alt M ⦄ ⦃ _ : Idiom M ⦄ → Maybe A → M .Effect.₀ A
maybe→alt (just x) = pure x
maybe→alt nothing  = fail
