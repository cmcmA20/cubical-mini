{-# OPTIONS --safe #-}
module Meta.Effect.Alt where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Choice
open import Meta.Effect.Bind
open import Meta.Effect.Idiom

open import Data.Bool.Base
open import Data.Unit.Base

private variable
  ℓ : Level
  A : Type ℓ

record Alt (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Choice-alt ⦄ : Choice M
    fail  : M.₀ A
open Alt ⦃ ... ⦄

module _ {M : Effect} (let module M = Effect M) ⦃ alt : Alt M ⦄ where
  open Bind ⦃ ... ⦄
  open Idiom ⦃ ... ⦄

  guard : ⦃ appl : Idiom M ⦄
        → Bool → M.₀ ⊤
  guard true  = pure tt
  guard false = fail

  guardM : ⦃ mon : Bind M ⦄
         → M.₀ Bool → M.₀ ⊤
  guardM M = M >>= guard
