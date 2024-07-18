{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Idiom where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom

open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Instances.Map public

instance
  Idiom-Vec : ∀ {n} → Idiom (eff (λ T → Vec T n))
  Idiom-Vec .pure = replicate _
  Idiom-Vec ._<*>_ {A} {B} = go where
    go : ∀ {@0 n} → Vec (A → B) n → Vec A n → Vec B n
    go []       []       = []
    go (f ∷ fs) (x ∷ xs) = f x ∷ go fs xs
