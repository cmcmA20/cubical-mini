{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Discrete where

open import Foundations.Base

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Dec.Base as Dec
open import Data.List.Base using ([]) renaming (_∷_ to _∷ₗ_)
open import Data.Vec.Inductive.Base

private variable
  ℓ : Level
  A : Type ℓ
  @0 n : ℕ

vec-is-discrete : ⦃ di : is-discrete A ⦄ → is-discrete (Vec A n)
vec-is-discrete {A} ⦃ di ⦄ = go _ _ where
  go : ∀ {@0 n} → (xs ys : Vec A n) → Dec (xs ＝ ys)
  go []       []       = yes refl
  go (x ∷ xs) (y ∷ ys) = Dec.dmap
    (λ (x=y , xs=ys) → ap² _∷_ x=y xs=ys)
    (λ f p → f (ap head p , ap tail p))
    (Dec-× ⦃ x ≟ y ⦄ ⦃ go xs ys ⦄)
