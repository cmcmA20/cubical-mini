{-# OPTIONS --safe #-}
module Data.List.Instances.Discrete where

open import Foundations.Base

open import Correspondences.Decidable
open import Correspondences.Discrete

open import Data.Dec.Base as Dec
open import Data.List.Base
open import Data.List.Path

private variable
  ℓ : Level
  A : Type ℓ

instance
  list-is-discrete : ⦃ di : is-discrete A ⦄ → is-discrete (List A)
  list-is-discrete {A} ⦃ di ⦄ = go where
    go : is-discrete (List A)
    go {([])}   {([])}   = yes refl
    go {([])}   {_ ∷ _}  = no $ ∷≠[] ∘ sym
    go {_ ∷ _}  {([])}   = no ∷≠[]
    go {x ∷ xs} {y ∷ ys} = Dec.dmap
      (λ (x=y , xs=ys) → ap² _∷_ x=y xs=ys)
      (λ f p → f (∷-head-inj p , ap tail p))
      (Dec-× ⦃ di ⦄ ⦃ go ⦄)
