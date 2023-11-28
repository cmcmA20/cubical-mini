{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Idiom where

open import Foundations.Base

open import Meta.Idiom

open import Data.Nat.Base

open import Data.Vec.Inductive.Base public

private variable
  ℓ : Level
  A : Type ℓ
  @0 n : ℕ

instance
  Map-Vec : Map (eff (λ T → Vec T n))
  Map-Vec .Map._<$>_ = map

  Idiom-Vec : {n : ℕ} → Idiom (eff (λ T → Vec T n))
  Idiom-Vec .Idiom.pure = replicate _
  Idiom-Vec .Idiom._<*>_ = go where
    go : {@0 n : ℕ} → Vec (_ → _) n → Vec _ n → Vec _ n
    go []       []       = []
    go (f ∷ fs) (x ∷ xs) = f x ∷ go fs xs
