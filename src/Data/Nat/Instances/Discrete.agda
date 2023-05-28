{-# OPTIONS --safe #-}
module Data.Nat.Instances.Discrete where

open import Foundations.Base

open import Meta.Discrete

open import Data.Dec.Base
open import Data.Id

open import Data.Nat.Base

instance
  Discrete-ℕ : Discrete ℕ
  Discrete-ℕ .Discrete._≟_ =
    is-discreteⁱ→is-discrete ℕ-is-discreteⁱ
    where
    ℕ-is-discreteⁱ : is-discreteⁱ ℕ
    ℕ-is-discreteⁱ zero    zero    = yes reflⁱ
    ℕ-is-discreteⁱ zero    (suc _) = no λ {()}
    ℕ-is-discreteⁱ (suc _) zero    = no λ {()}
    ℕ-is-discreteⁱ (suc m) (suc n) =
      map (λ { reflⁱ → reflⁱ })
          (λ { f reflⁱ → f reflⁱ })
          (ℕ-is-discreteⁱ m n)
