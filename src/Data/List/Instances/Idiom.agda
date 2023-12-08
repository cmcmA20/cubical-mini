{-# OPTIONS --safe #-}
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
  Idiom-List .Idiom.pure = _∷ []
  Idiom-List .Idiom._<*>_ = go where
    go : List (_ → _) → List _ → List _
    go (f ∷ fs) (x ∷ xs) = f x ∷ go fs xs
    go _        _        = []
