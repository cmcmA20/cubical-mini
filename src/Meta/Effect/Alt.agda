{-# OPTIONS --safe #-}
module Meta.Effect.Alt where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Bind
open import Meta.Effect.Idiom

open import Data.Bool.Base

private variable
  ℓ : Level
  A : Type ℓ

record Alt (M : Effect) : Typeω where
  private module M = Effect M
  field
    fail  : M.₀ A
    _<|>_ : M.₀ A → M.₀ A → M.₀ A
  infixl 3 _<|>_

open Alt ⦃ ... ⦄ public

module _ {M : Effect} (let module M = Effect M) ⦃ alt : Alt M ⦄ where

  guard : ⦃ appl : Idiom M ⦄
        → Bool → M.₀ ⊤
  guard true  = pure tt
  guard false = fail

  guardM : ⦃ mon : Bind M ⦄
         → M.₀ Bool → M.₀ ⊤
  guardM M = M >>= guard
