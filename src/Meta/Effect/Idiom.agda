{-# OPTIONS --safe #-}
module Meta.Effect.Idiom where

open import Foundations.Base

open import Meta.Effect.Map public

open import Data.Bool.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

record Idiom (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-idiom ⦄ : Map M
    pure  : A → M.₀ A
    _<*>_ : M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_

open Idiom ⦃ ... ⦄ public


module _ {M : Effect} (let module M = Effect M) ⦃ app : Idiom M ⦄ where
  when : Bool → M.₀ ⊤ → M.₀ ⊤
  when true  t = t
  when false _ = pure tt

  unless : Bool → M.₀ ⊤ → M.₀ ⊤
  unless false t = t
  unless true  _ = pure tt
