{-# OPTIONS --safe #-}
module Data.List.Instances.Idiom where

open import Foundations.Base
open import Meta.Idiom

open import Data.List.Base public

private variable
  ℓ : Level
  A : Type ℓ

instance
  Map-List : Map (eff List)
  Map-List .Map._<$>_ = map

  Idiom-List : Idiom (eff List)
  Idiom-List .Idiom.pure = _∷ []
  Idiom-List .Idiom._<*>_ = go where
    go : List (_ → _) → List _ → List _
    go (f ∷ fs) (x ∷ xs) = f x ∷ go fs xs
    go _        _        = []
