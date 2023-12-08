{-# OPTIONS --safe #-}
module Meta.Effect.Bind where

open import Foundations.Base

open import Meta.Effect.Idiom public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

record Bind (M : Effect) : Typeω where
  private module M = Effect M
  field
    _>>=_ : M.₀ A → (A → M.₀ B) → M.₀ B
    ⦃ Idiom-bind ⦄ : Idiom M

  _>>_ : M.₀ A → M.₀ B → M.₀ B
  _>>_ f g = f >>= λ _ → g

  _=<<_ : (A → M.₀ B) → M.₀ A → M.₀ B
  _=<<_ f x = x >>= f

open Bind ⦃ ... ⦄ public
