{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Idiom where

open import Foundations.Base

open import Meta.Effect.Idiom

open import Data.Vec.Inductive.Base
open import Data.Vec.Inductive.Instances.Map public

instance
  Idiom-Vec : ∀ {n} → Idiom (eff (λ T → Vec T n))
  Idiom-Vec .Idiom.pure = replicate _
  Idiom-Vec .Idiom._<*>_ = go where
    go : ∀ {@0 n} → Vec (_ → _) n → Vec _ n → Vec _ n
    go []       []       = []
    go (f ∷ fs) (x ∷ xs) = f x ∷ go fs xs
