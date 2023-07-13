{-# OPTIONS --safe #-}
module Meta.Idiom where

open import Foundations.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

record Effect : Typeω where
  constructor eff
  field
    {adj} : Level → Level
    ₀     : Type ℓ → Type (adj ℓ)

record Map (M : Effect) : Typeω where
  private module M = Effect M
  field
    _<$>_ : (A → B) → M.₀ A → M.₀ B

  infixl 4 _<$>_ _<&>_

  _<&>_ : M.₀ A → (A → B) → M.₀ B
  x <&> f = f <$> x


record Idiom (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-idiom ⦄ : Map M
    pure  : A → M.₀ A
    _<*>_ : M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_


open Map ⦃ ... ⦄ public
open Idiom ⦃ ... ⦄ public
