{-# OPTIONS --safe #-}
module Data.Nat.Instances.Decidable where

open import Foundations.Base

open import Meta.Search.Decidable

import Data.Dec.Base as Dec
open Dec
open import Data.Id

open import Data.Nat.Base

instance
  ℕ-is-discrete : is-discrete ℕ
  ℕ-is-discrete = is-discreteⁱ→is-discrete ℕ-is-discreteⁱ where
    ℕ-is-discreteⁱ : is-discreteⁱ ℕ
    ℕ-is-discreteⁱ 0 0       = yes reflⁱ
    ℕ-is-discreteⁱ 0 (suc _) = no λ()
    ℕ-is-discreteⁱ (suc _) 0 = no λ()
    ℕ-is-discreteⁱ (suc m) (suc n) =
      Dec.map (λ { reflⁱ → reflⁱ })
              (λ { f reflⁱ → f reflⁱ })
              (ℕ-is-discreteⁱ m n)
