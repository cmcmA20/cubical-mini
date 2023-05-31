{-# OPTIONS --safe #-}
module Data.Fin.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete

open import Data.Dec.Base
open import Data.Id

open import Data.Fin.Base

instance
  Discrete-Fin : {n : ℕ} → Discrete (Fin n)
  Discrete-Fin .Discrete._≟_ =
    is-discreteⁱ→is-discrete Fin-is-discreteⁱ
    where
    Fin-is-discreteⁱ : {n : ℕ} → is-discreteⁱ (Fin n)
    Fin-is-discreteⁱ fzero    fzero    = yes reflⁱ
    Fin-is-discreteⁱ fzero    (fsuc _) = no λ ()
    Fin-is-discreteⁱ (fsuc _) fzero    = no λ ()
    Fin-is-discreteⁱ (fsuc k) (fsuc l) =
      map (apⁱ fsuc)
          (λ { p reflⁱ → p reflⁱ })
          (Fin-is-discreteⁱ k l)
