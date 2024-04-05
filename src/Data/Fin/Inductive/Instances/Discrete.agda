{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Instances.Discrete where

open import Foundations.Base

open import Correspondences.Discrete

open import Data.Dec.Base as Dec
open import Data.Id.Inductive

open import Data.Fin.Inductive.Base

private variable @0 n : ℕ

instance
  fin-is-discrete : is-discrete (Fin n)
  fin-is-discrete = is-discreteⁱ→is-discrete fin-is-discreteⁱ where
    fin-is-discreteⁱ : is-discreteⁱ (Fin n)
    fin-is-discreteⁱ fzero    fzero    = yes reflⁱ
    fin-is-discreteⁱ fzero    (fsuc _) = no λ ()
    fin-is-discreteⁱ (fsuc _) fzero    = no λ ()
    fin-is-discreteⁱ (fsuc k) (fsuc l) =
      Dec.dmap (apⁱ fsuc)
               (_∘ (λ { reflⁱ → reflⁱ }))
               (fin-is-discreteⁱ k l)
