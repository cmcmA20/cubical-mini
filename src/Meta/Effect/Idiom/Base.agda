{-# OPTIONS --safe #-}
module Meta.Effect.Idiom.Base where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Map.Base

open import Data.Bool.Base
open import Data.Unit.Base

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ
  F : A → Type ℓᶜ

record Idiom (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-idiom ⦄ : Map M
    pure  : A → M.₀ A
    _<*>_ : M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_
open Idiom ⦃ ... ⦄

module _ {M : Effect} (let module M = Effect M) ⦃ app : Idiom M ⦄ where
  when : Bool → M.₀ ⊤ → M.₀ ⊤
  when true  t = t
  when false _ = pure tt

  unless : Bool → M.₀ ⊤ → M.₀ ⊤
  unless false t = t
  unless true  _ = pure tt

  map² : (A → B → C) → M.₀ A → M.₀ B → M.₀ C
  map² f x y = ⦇ f x y ⦈

  map³ : (A → B → C → D) → M.₀ A → M.₀ B → M.₀ C → M.₀ D
  map³ f x y z = ⦇ f x y z ⦈

instance
  Idiom-Erased : Idiom (eff λ T → Erased T)
  Idiom-Erased .pure x = erase x
  Idiom-Erased ._<*>_ (erase f) (erase x) .erased = f x

Idiom-Id : Idiom (eff id)
Idiom-Id .Idiom.Map-idiom = Map-Id
Idiom-Id .Idiom.pure x = x
Idiom-Id .Idiom._<*>_ f x = f x
-- {-# INCOHERENT Idiom-Id #-}

module _ {M N : Effect} (let module M = Effect M; module N = Effect N)
         ⦃ _ : Idiom M ⦄ ⦃ _ : Idiom N ⦄ where

  Idiom-Compose : Idiom (eff (M.₀ ∘ N.₀))
  Idiom-Compose .Idiom.Map-idiom = Map-Compose
  Idiom-Compose .Idiom.pure x = pure (pure x)
  Idiom-Compose .Idiom._<*>_ f x = pure _<*>_ <*> f <*> x
