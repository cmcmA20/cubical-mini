{-# OPTIONS --safe #-}
module Data.List.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Correspondences.Decidable

open import Data.Dec.Base as Dec
open import Data.List.Base
open import Data.List.Path

private variable
  ℓ : Level
  A : Type ℓ


list-is-discrete : is-discrete A → is-discrete (List A)
list-is-discrete di = is-discrete-η go where
  go : _
  go []       []       = yes refl
  go []       (_ ∷ _)  = no $ ∷≠[] ∘ sym
  go (_ ∷ _)  []       = no ∷≠[]
  go (x ∷ xs) (y ∷ ys) = Dec.dmap
    (λ (x=y , xs=ys) → ap² _∷_ x=y xs=ys)
    (λ f p → f (∷-head-inj p , ap tail p))
    (×-decision (di .is-discrete-β x y) $ go xs ys)

instance
  decomp-dis-list : goal-decomposition (quote is-discrete) (List A)
  decomp-dis-list = decomp (quote list-is-discrete) (`search (quote is-discrete) ∷ [])
