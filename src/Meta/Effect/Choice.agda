{-# OPTIONS --safe #-}
module Meta.Effect.Choice where

open import Foundations.Base

open import Meta.Effect.Base

private variable
  ℓ : Level
  A : Type ℓ

record Choice (M : Effect) : Typeω where
  private module M = Effect M
  field
    _<|>_ : M.₀ A → M.₀ A → M.₀ A
  infixl 3 _<|>_
open Choice ⦃ ... ⦄
