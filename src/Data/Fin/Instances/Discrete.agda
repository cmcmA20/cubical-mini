{-# OPTIONS --safe #-}
module Data.Fin.Instances.Discrete where

open import Foundations.Base

open import Meta.Decision

open import Data.Dec.Base
open import Data.Id

open import Data.Fin.Base

instance
  Discrete-Fin : {@0 n : ℕ} → Discrete (Fin n)
  Discrete-Fin .Decision.has-decidable =
    is-discreteⁱ→is-discrete Fin-is-discreteⁱ
    where
    Fin-is-discreteⁱ : {@0 n : ℕ} → is-discreteⁱ (Fin n)
    Fin-is-discreteⁱ fzero    fzero    = yes reflⁱ
    Fin-is-discreteⁱ fzero    (fsuc _) = no λ ()
    Fin-is-discreteⁱ (fsuc _) fzero    = no λ ()
    Fin-is-discreteⁱ (fsuc k) (fsuc l) =
      map (apⁱ fsuc)
          (λ { p reflⁱ → p reflⁱ })
          (Fin-is-discreteⁱ k l)
