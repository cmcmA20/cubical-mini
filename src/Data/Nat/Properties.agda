{-# OPTIONS --safe #-}
module Data.Nat.Properties where

open import Foundations.Base

open import Data.Dec.Base
open import Data.Id

open import Data.Nat.Base public

ℕ-is-discreteⁱ : is-discreteⁱ ℕ
ℕ-is-discreteⁱ zero    zero    = yes reflⁱ
ℕ-is-discreteⁱ zero    (suc _) = no λ {()}
ℕ-is-discreteⁱ (suc _) zero    = no λ {()}
ℕ-is-discreteⁱ (suc m) (suc n) =
  map (λ { reflⁱ → reflⁱ })
          (λ { f reflⁱ → f reflⁱ })
          (ℕ-is-discreteⁱ m n)
