{-# OPTIONS --safe #-}
module Meta.Effect.Monoidal where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map
open import Meta.Effect.Idiom

open import Data.Unit.Base

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

record Monoidal (M : Effect) : Typeω where
  private module M = Effect M
  field
    unit  : M.₀ ⊤
    _<,>_ : M.₀ A → M.₀ B → M.₀ (A × B)

  infixr 4 _<,>_

open Monoidal ⦃ ... ⦄ public

instance
  Monoidal-Idiom : {M : Effect} → ⦃ Idiom M ⦄ → Monoidal M
  Monoidal-Idiom .unit = pure tt
  Monoidal-Idiom ._<,>_ ma mb = ⦇ ma , mb ⦈
  {-# OVERLAPPABLE Monoidal-Idiom #-}
