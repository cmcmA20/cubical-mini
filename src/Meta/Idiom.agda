{-# OPTIONS --safe #-}
module Meta.Idiom where

open import Foundations.Base

record Effect : Typeω where
  constructor eff
  field
    {adj} : Level → Level
    ₀     : ∀ {ℓ} → Type ℓ → Type (adj ℓ)

record Map (M : Effect) : Typeω where
  private module M = Effect M
  field
    _<$>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → (A → B) → M.₀ A → M.₀ B

  infixl 4 _<$>_ _<&>_

  _<&>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → M.₀ A → (A → B) → M.₀ B
  x <&> f = f <$> x


record Idiom (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-idiom ⦄ : Map M
    pure  : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    _<*>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_


open Map ⦃ ... ⦄ public
open Idiom ⦃ ... ⦄ public
