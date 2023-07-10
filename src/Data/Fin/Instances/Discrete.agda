{-# OPTIONS --safe #-}
module Data.Fin.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base
open import Data.Id

open import Data.Fin.Base

instance
  fin-is-discrete : {@0 n : ℕ} → is-discrete (Fin n)
  fin-is-discrete = is-discreteⁱ→is-discrete fin-is-discreteⁱ where
    fin-is-discreteⁱ : {@0 n : ℕ} → is-discreteⁱ (Fin n)
    fin-is-discreteⁱ fzero    fzero    = yes reflⁱ
    fin-is-discreteⁱ fzero    (fsuc _) = no λ ()
    fin-is-discreteⁱ (fsuc _) fzero    = no λ ()
    fin-is-discreteⁱ (fsuc k) (fsuc l) =
      map (apⁱ fsuc)
          (λ { p reflⁱ → p reflⁱ })
          (fin-is-discreteⁱ k l)
