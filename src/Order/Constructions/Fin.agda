{-# OPTIONS --safe #-}
module Order.Constructions.Fin where

open import Cat.Prelude
open import Order.Base
open import Order.Total
open import Order.Displayed
open import Order.Constructions.Nat

open import Data.Nat.Order.Base
open import Data.Fin.Computational

open Displayed public

Finₚ-over : Displayed 0ℓ 0ℓ ℕₚ
Ob[ Finₚ-over ] n = Fin n
Rel[ Finₚ-over ] x≤y fx fy = fin→ℕ fx ≤ fin→ℕ fy
Finₚ-over .≤-refl' = ≤-refl
Finₚ-over .≤-thin' x≤y = hlevel 1
Finₚ-over .≤-trans' = ≤-trans
Finₚ-over .≤-antisym' fx≤fy fy≤fx = fin-ext $ ≤-antisym fx≤fy fy≤fx

Finₚ : Poset 0ℓ 0ℓ
Finₚ = ∫ Finₚ-over

