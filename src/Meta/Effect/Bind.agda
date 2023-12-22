{-# OPTIONS --safe #-}
module Meta.Effect.Bind where

open import Foundations.Base

open import Meta.Effect.Idiom public

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

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


instance
  Bind-Erased : Bind (eff λ T → Erased T)
  Bind-Erased ._>>=_ (erase x) mf .erased = mf x .erased
