{-# OPTIONS --safe #-}
module Meta.Effect.Container where

open import Foundations.Prelude
open import Meta.Effect.Base

open import Data.Container.Base
open import Data.Container.Instances.Brackets

record Abstract-Container (M : Effect) : Typeω where
  no-eta-equality
  constructor make-abstract-container
  private module M = Effect M
  field
    {ℓs ℓp} : Level
    con : Container ℓs ℓp
    has-abs-con : {ℓ : Level} {X : Type ℓ} → M.₀ X ≃ ⟦ con ⟧ X
{-# INLINE make-abstract-container #-}
