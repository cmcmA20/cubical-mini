{-# OPTIONS --safe #-}
module Meta.Effect.Alternative where

open import Foundations.Base

open import Meta.Effect.Alt
open import Meta.Effect.Base
open import Meta.Effect.Map

open import Data.Empty.Base
open import Data.Sum.Base

private variable
  ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ

record Alternative (M : Effect) : Typeω where
  private module M = Effect M
  field
    empty : M.₀ ⊥
    _<+>_ : M.₀ A → M.₀ B → M.₀ (A ⊎ B)

  infixr 3 _<+>_

open Alternative ⦃ ... ⦄ public

instance
  Alternative-Alt : {M : Effect} → ⦃ Map M ⦄ → ⦃ Alt M ⦄ → Alternative M
  Alternative-Alt .empty = fail
  Alternative-Alt ._<+>_ ma mb = inl <$> ma <|> inr <$> mb
  {-# INCOHERENT Alternative-Alt #-}
