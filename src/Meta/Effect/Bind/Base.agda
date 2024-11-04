{-# OPTIONS --safe #-}
module Meta.Effect.Bind.Base where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

record Bind (M : Effect) : Typeω where
  private module M = Effect M
  infixl 1 _>>=_
  field
    _>>=_ : M.₀ A → (A → M.₀ B) → M.₀ B
    ⦃ Idiom-bind ⦄ : Idiom M

  _>>_ : M.₀ A → M.₀ B → M.₀ B
  _>>_ f g = f >>= λ _ → g

  infixr 1 _=<<_
  _=<<_ : (A → M.₀ B) → M.₀ A → M.₀ B
  _=<<_ f x = x >>= f

open Bind ⦃ ... ⦄

instance
  Bind-Erased : Bind (eff λ T → Erased T)
  Bind-Erased ._>>=_ (erase x) mf .erased = mf x .erased
