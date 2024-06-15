{-# OPTIONS --safe --no-exact-split #-}
module Data.List.Instances.Idiom where

open import Foundations.Base

open import Meta.Effect.Idiom

open import Data.List.Base
open import Data.List.Instances.Map public

private variable
  ℓ : Level
  A : Type ℓ

instance
  Idiom-List : Idiom (eff List)
  Idiom-List .pure = _∷ []
  Idiom-List ._<*>_ {A} {B} = go where
    go : List (A → B) → List A → List B
    go (f ∷ fs) (x ∷ xs) = f x ∷ go fs xs
    go _        _        = []
